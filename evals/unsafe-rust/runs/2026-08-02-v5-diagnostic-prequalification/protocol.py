#!/usr/bin/env python3
"""Executable DRAFT protocol for V5 diagnostic prequalification.

The protocol deliberately does not turn this shared-filesystem collaboration
environment into an admissible evaluator.  It does provide the strongest
coordinator-side mechanics available here: one exclusive started-attempt
lease, complete envelope capture, and a first-terminal content-addressed
canonical pointer.  The executable gate manifest independently fixes the
isolation and output-finalization roots to FAIL.

When this trusted file is run from the DRAFT source tree, mutable synthetic
state must be placed under an explicit external directory.  Production
operations must use this trusted source copy, a separately custodied external
commitment, and a separately finalized bundle whose trusted verifier
authenticates a PRODUCTION static lock.  They may mutate only that bundle's
exact ``runtime/state`` carve-out.  A protocol copy inside a candidate bundle
is data to authenticate, never an executable trust anchor.  Static validation
and synthetic self-tests do not create source-run artifacts.
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
import shutil
import stat
import sys
import tempfile
import types
import unicodedata
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path, PurePosixPath
from typing import Any, Callable, Iterator


RUN = Path(__file__).resolve().parent
RUNTIME_ROOT = RUN / "runtime"
MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
LABELS = tuple(chr(ord("A") + index) for index in range(15))
SCORERS = ("s1", "s2")
CONSISTENCY_REVIEWERS = ("c1", "c2")
MATERIALITY_REVIEWERS = ("m1", "m2")
GLOBAL_EVALUATOR_ROLES = ("materiality-reviewer", "materiality-adjudicator")
SEMANTIC_AGENT_ROLES = (
    "report",
    "scorer",
    "consistency",
    "adjudicator",
    *GLOBAL_EVALUATOR_ROLES,
)
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
PRODUCTION_ACTOR_ID = re.compile(r"^[a-z0-9][a-z0-9._-]{15,127}$")
ATOM_ID = re.compile(r"^[EVFPBLRQ][1-9][0-9]*$")
HEX64 = re.compile(r"^[0-9a-f]{64}$")
REPORT_RUN_ID = re.compile(r"^r(?:00[1-9]|0[1-9][0-9]|1[01][0-9]|120)$")
PACKET_KINDS = (
    "SCORER-INPUT",
    "CONSISTENCY-INPUT",
    "ADJUDICATION-INPUT",
    "MATERIALITY-REVIEW-INPUT",
    "MATERIALITY-ADJUDICATION-INPUT",
)
AGGREGATE_DIGEST_KEYS = (
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
)
AGGREGATE_BUILDER_ID = "v5-diagnostic-aggregate-context-v1"
PROJECTION_INVENTORY_BUILDER_ID = "v5-report-secret-inventory-v1"
SCORE_RESOURCE_PATHS = {
    "projection_bundle": "resources/projection-index.json",
    "atom_manifest": "resources/atom-manifest.json",
    "defect_rules": "resources/defect-rules.json",
    "oracle": "resources/oracle.md",
    "allowlist": "resources/allowlist.txt",
    "evaluator_authority": "resources/evaluator-authority.json",
    "presentation_order": "resources/presentation-order.json",
}

REQUIRED_ROOT_ORDER = (
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
)
REQUIRED_ROOT_IDS = set(REQUIRED_ROOT_ORDER)
ROOT_REQUIREMENT_SOURCES = {
    "G-ISOLATION": "testing-plan:artifact-architecture",
    "G-OUTPUT-FINALIZATION": "testing-plan:fresh-agent-protocol",
    "D-STATIC-INTEGRITY": "run-specific",
    "D-ORACLE-COVERAGE": "diagnostic-design",
    "D-COLLECTION-COMPLETE": "run-specific",
    "D-OUTPUT-VALID": "attempt-envelope.schema.json+aggregation-rules.json",
    "D-FOCUSED-RECALL": "diagnostic-design",
    "D-PROOF-QUALITY": "diagnostic-design",
    "D-CONTROLS": "diagnostic-design",
    "D-NO-HARD-ERROR": "aggregation-rules.json",
    "D-NO-GLOBAL-DEFECT": "aggregation-rules.json",
    "D-NO-MATERIAL-FINDING": "diagnostic-design",
    "D-COMPARISON": "comparison-predicate.json",
    "D-COHERENCE": "diagnostic-design",
    "D-DIAGNOSTIC-COMPLETION": "run-specific",
}


def gate_input(input_id: str, input_type: str, path: str) -> dict[str, Any]:
    return {
        "id": input_id,
        "type": input_type,
        "source": {"kind": "context", "path": path},
    }


EXPECTED_GATE_MECHANICS = {
    "G-ISOLATION": {
        "prerequisites": [],
        "inputs": [],
        "predicate": {"kind": "constant", "outcome": "FAIL"},
    },
    "G-OUTPUT-FINALIZATION": {
        "prerequisites": [],
        "inputs": [],
        "predicate": {"kind": "constant", "outcome": "FAIL"},
    },
    "D-STATIC-INTEGRITY": {
        "prerequisites": [],
        "inputs": [],
        "predicate": {"kind": "verified_bound_context"},
    },
    "D-ORACLE-COVERAGE": {
        "prerequisites": ["D-STATIC-INTEGRITY"],
        "inputs": [gate_input("oracle_coverage", "boolean", "oracle.coverage_pass")],
        "predicate": {"kind": "boolean_true", "input": "oracle_coverage"},
    },
    "D-COLLECTION-COMPLETE": {
        "prerequisites": ["D-STATIC-INTEGRITY"],
        "inputs": [gate_input("collection_complete", "boolean", "collection.complete")],
        "predicate": {"kind": "boolean_true", "input": "collection_complete"},
    },
    "D-OUTPUT-VALID": {
        "prerequisites": ["D-COLLECTION-COMPLETE"],
        "inputs": [gate_input("invalid_output_count", "integer", "collection.invalid_output_count")],
        "predicate": {"kind": "integer_equals", "input": "invalid_output_count", "value": 0},
    },
    "D-FOCUSED-RECALL": {
        "prerequisites": [
            "D-ORACLE-COVERAGE",
            "D-COLLECTION-COMPLETE",
            "D-OUTPUT-VALID",
        ],
        "inputs": [gate_input("focused_recall", "boolean", "scores.focused_recall_pass")],
        "predicate": {"kind": "boolean_true", "input": "focused_recall"},
    },
    "D-PROOF-QUALITY": {
        "prerequisites": ["D-COLLECTION-COMPLETE", "D-OUTPUT-VALID"],
        "inputs": [gate_input("proof_quality", "boolean", "scores.proof_quality_pass")],
        "predicate": {"kind": "boolean_true", "input": "proof_quality"},
    },
    "D-CONTROLS": {
        "prerequisites": ["D-COLLECTION-COMPLETE", "D-OUTPUT-VALID"],
        "inputs": [gate_input("controls", "boolean", "scores.controls_pass")],
        "predicate": {"kind": "boolean_true", "input": "controls"},
    },
    "D-NO-HARD-ERROR": {
        "prerequisites": ["D-COLLECTION-COMPLETE"],
        "inputs": [gate_input("hard_error_count", "integer", "scores.hard_error_count")],
        "predicate": {"kind": "integer_equals", "input": "hard_error_count", "value": 0},
    },
    "D-NO-GLOBAL-DEFECT": {
        "prerequisites": ["D-COLLECTION-COMPLETE"],
        "inputs": [gate_input("global_defect_count", "integer", "scores.global_defect_count")],
        "predicate": {"kind": "integer_equals", "input": "global_defect_count", "value": 0},
    },
    "D-NO-MATERIAL-FINDING": {
        "prerequisites": ["D-COLLECTION-COMPLETE"],
        "inputs": [gate_input("material_finding_count", "integer", "scores.material_finding_count")],
        "predicate": {"kind": "integer_equals", "input": "material_finding_count", "value": 0},
    },
    "D-COMPARISON": {
        "prerequisites": ["D-COLLECTION-COMPLETE"],
        "inputs": [gate_input("comparison", "boolean", "comparison.predicate_pass")],
        "predicate": {"kind": "boolean_true", "input": "comparison"},
    },
    "D-COHERENCE": {
        "prerequisites": ["D-STATIC-INTEGRITY"],
        "inputs": [gate_input("coherence", "boolean", "review.coherence_pass")],
        "predicate": {"kind": "boolean_true", "input": "coherence"},
    },
    "D-DIAGNOSTIC-COMPLETION": {
        "prerequisites": list(REQUIRED_ROOT_ORDER[2:-1]),
        "inputs": [],
        "predicate": {"kind": "constant", "outcome": "PASS"},
    },
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
INTEGRATION_HOOK_PHASES = {
    "H-RECOMPUTE-PACKAGE-TREES": "SNAPSHOT_BUILD",
    "H-VERIFY-SKILL-BYTES": "SNAPSHOT_BUILD",
    "H-RECOMPUTE-TARGET-TREES": "SNAPSHOT_BUILD",
    "H-MATERIALIZE-OPAQUE-TARGETS-AND-SCAN-LEAKAGE": "SNAPSHOT_BUILD",
    "H-VALIDATE-READY-STATUS": "SNAPSHOT_BUILD",
    "H-VALIDATE-CROSS-REFERENCE-CLOSURE": "SNAPSHOT_REVIEW",
    "H-VALIDATE-HIDDEN-FIXTURE-MANIFESTS": "SNAPSHOT_REVIEW",
    "H-VALIDATE-ORACLE-COVERAGE": "SNAPSHOT_REVIEW",
    "H-VALIDATE-INDEPENDENT-SIGNOFFS": "SNAPSHOT_REVIEW",
    "H-BUILD-VALIDATE-REPORT-AUTHORITY-PROJECTIONS": "SNAPSHOT_REVIEW",
    "H-VALIDATE-PROMPT-RENDERINGS": "SNAPSHOT_REVIEW",
    "H-FREEZE-VALIDATE-ENVELOPE-SPECS": "SNAPSHOT_BUILD",
    "H-FREEZE-EXECUTION-ENVIRONMENT-MANIFESTS": "SNAPSHOT_BUILD",
    "H-ENFORCE-WORD-COUNTER": "RUNTIME_COLLECTION",
    "H-BUILD-VALIDATE-SCORER-REPORT-PROJECTIONS": "RUNTIME_COLLECTION",
    "H-GENERATE-VERIFY-RANDOMIZATION": "SNAPSHOT_REVIEW",
    "H-VALIDATE-SCHEDULE-LEASE-ATTEMPT-LEDGER": "RUNTIME_COLLECTION",
    "H-SEMANTICALLY-REVALIDATE-ENVELOPES": "RUNTIME_COLLECTION",
    "H-VALIDATE-EVALUATOR-INDEPENDENCE-QUALIFICATION": "RUNTIME_COLLECTION",
    "H-RUN-VALIDATE-MATERIALITY-REVIEWS": "POSTRUN_AGGREGATE",
    "H-BUILD-WHOLE-FILE-MANIFEST": "FINALIZE_STATIC",
    "H-CREATE-LOCK-LAST": "FINALIZE_STATIC",
    "H-DERIVE-AGGREGATE-CONTEXT": "POSTRUN_AGGREGATE",
    "H-VALIDATE-AGGREGATION-RULE-INVENTORY": "SNAPSHOT_REVIEW",
    "H-BIND-CONTEXT-INPUT-DIGESTS": "POSTRUN_AGGREGATE",
}
INTEGRATION_PHASES = (
    "SNAPSHOT_BUILD",
    "SNAPSHOT_REVIEW",
    "FINALIZE_STATIC",
    "RUNTIME_COLLECTION",
    "POSTRUN_AGGREGATE",
)
POSTLOCK_RECEIPT_HOOK_IDS = tuple(
    hook_id
    for hook_id in EXPECTED_INTEGRATION_HOOK_IDS
    if INTEGRATION_HOOK_PHASES[hook_id]
    in ("RUNTIME_COLLECTION", "POSTRUN_AGGREGATE")
)
PRE_BIND_RECEIPT_HOOK_IDS = tuple(
    hook_id
    for hook_id in POSTLOCK_RECEIPT_HOOK_IDS
    if hook_id != "H-BIND-CONTEXT-INPUT-DIGESTS"
)


class ProtocolError(RuntimeError):
    """Base class for fail-closed protocol errors."""


class LeaseAlreadyExists(ProtocolError):
    """A slot already has a started-attempt lease; retry is forbidden."""


class CanonicalAlreadySealed(ProtocolError):
    """A first-terminal canonical envelope already exists for the slot."""


class TerminalAlreadyClaimed(ProtocolError):
    """A seal operation already claimed the attempt's one terminal transition."""


class InjectedFault(ProtocolError):
    """Synthetic crash point used only by protocol fault-injection tests."""


_SYNTHETIC_TEST_CAPABILITY = object()


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def reject_json_constant(value: str) -> None:
    raise ProtocolError(f"non-finite JSON number is forbidden: {value}")


def reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ProtocolError(f"duplicate JSON key is forbidden: {key!r}")
        result[key] = value
    return result


def strict_json_loads(data: bytes | str, label: str = "JSON") -> Any:
    if isinstance(data, bytes):
        try:
            text = data.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise ProtocolError(f"{label} is not strict UTF-8") from error
    elif isinstance(data, str):
        text = data
    else:
        raise ProtocolError(f"{label} input must be bytes or text")
    try:
        return json.loads(
            text,
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_json_constant,
        )
    except ProtocolError:
        raise
    except json.JSONDecodeError as error:
        raise ProtocolError(f"{label} is not valid JSON") from error


def canonical_json_bytes(value: Any) -> bytes:
    try:
        encoded = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
    except (TypeError, ValueError) as error:
        raise ProtocolError("value is not canonical finite JSON") from error
    return (encoded + "\n").encode("utf-8")


def pretty_json(value: Any) -> str:
    try:
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
    except (TypeError, ValueError) as error:
        raise ProtocolError("value is not finite JSON") from error


def read_json(path: Path) -> Any:
    return strict_json_loads(path.read_bytes(), str(path))


def require_exact_keys(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        actual = sorted(value) if isinstance(value, dict) else type(value).__name__
        raise ProtocolError(f"{label} keys mismatch: {actual!r}")
    return value


def require_safe_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or not SAFE_ID.fullmatch(value):
        raise ProtocolError(f"invalid {label}: {value!r}")
    return value


def require_production_actor_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or PRODUCTION_ACTOR_ID.fullmatch(value) is None:
        raise ProtocolError(
            f"{label} must use the canonical 16-128 byte lowercase ASCII identity grammar"
        )
    return value


def reject_reviewer_runtime_reuse(
    agent_id: str, reviewer_ids: set[str] | frozenset[str]
) -> None:
    if agent_id in reviewer_ids:
        raise ProtocolError(
            "a source/snapshot reviewer identity is permanently ineligible for runtime semantic roles"
        )


def require_relative_file(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value or value != value.strip():
        raise ProtocolError(f"{label} must be a nonblank relative POSIX path")
    path = PurePosixPath(value)
    if (
        path.is_absolute()
        or path.as_posix() != value
        or "\\" in value
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


def require_normalized_absolute_path_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value or not Path(value).is_absolute():
        raise ProtocolError(f"{label} must be a nonblank absolute path string")
    normalized = os.path.normpath(value)
    if normalized != value:
        raise ProtocolError(f"{label} must be lexically normalized: {value!r}")
    return value


def require_external_path(path: Path, label: str) -> Path:
    resolved = path.resolve()
    if is_within(resolved, RUN):
        raise ProtocolError(f"DRAFT {label} must be outside the entire run tree: {resolved}")
    return resolved


def require_state_context(
    path: Path,
    *,
    static_root: Path | None = None,
    external_commitment_path: Path | None = None,
    test_capability: object | None = None,
) -> tuple[Path, Path | None, frozenset[str] | None]:
    """Bind state and reviewer exclusions in one coherent static verification."""

    lexical = Path(os.path.abspath(os.fspath(path)))
    if static_root is not None:
        root, _lock, reviewer_ids = load_verified_static_bundle(
            static_root, external_commitment_path
        )
        runtime_state = root / "runtime" / "state"
        if lexical != runtime_state:
            raise ProtocolError(
                "production state root is not the verified bundle runtime/state"
            )
        for component in (root / "runtime", runtime_state):
            if component.exists() and component.is_symlink():
                raise ProtocolError("runtime/state path components must not be symlinks")
        return lexical, root, reviewer_ids
    if test_capability is not _SYNTHETIC_TEST_CAPABILITY:
        raise ProtocolError(
            "state operation requires an explicit verified PRODUCTION static root"
        )
    resolved = path.resolve()
    if is_within(resolved, RUN):
        raise ProtocolError("external protocol state root resolves inside the run tree")
    return resolved, None, None


def require_state_root(
    path: Path,
    *,
    static_root: Path | None = None,
    external_commitment_path: Path | None = None,
    test_capability: object | None = None,
) -> Path:
    """Compatibility wrapper returning the state path from a coherent context."""

    state_root, _verified_root, _reviewer_ids = require_state_context(
        path,
        static_root=static_root,
        external_commitment_path=external_commitment_path,
        test_capability=test_capability,
    )
    return state_root


def run_trusted_module(name: str, run_name: str) -> dict[str, Any]:
    """Execute a harness module from this running protocol's trust root only."""

    if name not in {"integrate.py", "prepare.py", "word_count.py"}:
        raise ProtocolError(f"unsupported trusted harness module: {name}")
    path = RUN / name
    if path.is_symlink() or not path.is_file():
        raise ProtocolError(f"trusted harness module is not a regular file: {path}")
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        return runpy.run_path(str(path), run_name=run_name)
    finally:
        sys.dont_write_bytecode = previous


def trusted_integration_module() -> dict[str, Any]:
    """Load integrate.py while pinning its local imports to trusted source bytes."""

    trusted_prepare_values = run_trusted_module(
        "prepare.py", "v5_trusted_prepare_dependency"
    )
    trusted_word_count_values = run_trusted_module(
        "word_count.py", "v5_trusted_word_count_dependency"
    )
    trusted_prepare = types.ModuleType("prepare")
    trusted_prepare.__dict__.update(trusted_prepare_values)
    trusted_word_count = types.ModuleType("word_count")
    trusted_word_count.__dict__.update(trusted_word_count_values)
    saved = {name: sys.modules.get(name) for name in ("prepare", "word_count")}
    sys.modules["prepare"] = trusted_prepare
    sys.modules["word_count"] = trusted_word_count
    try:
        return run_trusted_module("integrate.py", "v5_trusted_integrate")
    finally:
        for name, module in saved.items():
            if module is None:
                sys.modules.pop(name, None)
            else:
                sys.modules[name] = module


def require_production_runtime_actor(
    value: Any,
    label: str,
    reviewer_ids: set[str] | frozenset[str],
) -> str:
    """Enforce the canonical actor domain and permanent reviewer exclusion."""

    actor_id = require_production_actor_id(value, label)
    reject_reviewer_runtime_reuse(actor_id, reviewer_ids)
    return actor_id


def maybe_inject_fault(fault_after: str | None, point: str) -> None:
    if fault_after == point:
        raise InjectedFault(f"synthetic fault after {point}")


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
    stage = path.parent / f".exclusive-stage-{path.name}-{secrets.token_hex(12)}"
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, "O_NOFOLLOW", 0)
    try:
        fd = os.open(stage, flags, 0o600)
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
        os.link(stage, path, follow_symlinks=False)
        fsync_directory(path.parent)
    finally:
        try:
            stage.unlink()
        except FileNotFoundError:
            pass
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


def build_packet_tree_manifest(
    packet_kind: str, packet_id: str, files: dict[str, bytes]
) -> dict[str, Any]:
    """Build a self-contained readable content-addressed packet manifest."""

    if packet_kind not in PACKET_KINDS:
        raise ProtocolError(f"unknown packet kind: {packet_kind!r}")
    require_safe_id(packet_id, "packet ID")
    if not isinstance(files, dict) or not files:
        raise ProtocolError("packet tree must contain at least one file")
    records: list[dict[str, Any]] = []
    for path in sorted(files):
        require_relative_file(path, "packet file path")
        data = files[path]
        if not isinstance(data, bytes):
            raise ProtocolError(f"packet file {path} must be bytes")
        try:
            content = data.decode("utf-8", errors="strict")
            encoding = "UTF8"
        except UnicodeDecodeError:
            content = base64.b64encode(data).decode("ascii")
            encoding = "BASE64"
        records.append(
            {
                "path": path,
                "size": len(data),
                "sha256": sha256(data),
                "encoding": encoding,
                "content": content,
            }
        )
    core = {
        "schema_version": 1,
        "status": "CONTENT-ADDRESSED",
        "packet_kind": packet_kind,
        "packet_id": packet_id,
        "files": records,
    }
    return {**core, "binding_sha256": sha256(canonical_json_bytes(core))}


def validate_packet_tree_manifest(
    value: Any, expected_kind: str | None = None
) -> dict[str, Any]:
    manifest = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "packet_kind",
            "packet_id",
            "files",
            "binding_sha256",
        },
        "packet tree manifest",
    )
    if (
        manifest["schema_version"] != 1
        or manifest["status"] != "CONTENT-ADDRESSED"
        or manifest["packet_kind"] not in PACKET_KINDS
        or (expected_kind is not None and manifest["packet_kind"] != expected_kind)
    ):
        raise ProtocolError("packet tree identity/status mismatch")
    require_safe_id(manifest["packet_id"], "packet ID")
    if not isinstance(manifest["files"], list) or not manifest["files"]:
        raise ProtocolError("packet tree files must be a nonempty list")
    paths: list[str] = []
    for raw in manifest["files"]:
        record = require_exact_keys(
            raw, {"path", "size", "sha256", "encoding", "content"}, "packet file"
        )
        path = require_relative_file(record["path"], "packet file path")
        if (
            type(record["size"]) is not int
            or record["size"] < 0
            or not isinstance(record["sha256"], str)
            or not HEX64.fullmatch(record["sha256"])
            or record["encoding"] not in ("UTF8", "BASE64")
            or not isinstance(record["content"], str)
        ):
            raise ProtocolError(f"packet file metadata is invalid: {path}")
        if record["encoding"] == "UTF8":
            data = record["content"].encode("utf-8")
        else:
            try:
                data = base64.b64decode(record["content"], validate=True)
            except Exception as error:
                raise ProtocolError(f"packet file base64 is invalid: {path}") from error
        if len(data) != record["size"] or sha256(data) != record["sha256"]:
            raise ProtocolError(f"packet file content binding mismatch: {path}")
        paths.append(path)
    if paths != sorted(paths) or len(paths) != len(set(paths)):
        raise ProtocolError("packet file paths must be unique and sorted")
    core = {key: manifest[key] for key in manifest if key != "binding_sha256"}
    if (
        not isinstance(manifest["binding_sha256"], str)
        or not HEX64.fullmatch(manifest["binding_sha256"])
        or manifest["binding_sha256"] != sha256(canonical_json_bytes(core))
    ):
        raise ProtocolError("packet tree binding digest mismatch")
    return manifest


def packet_file_bytes(manifest: dict[str, Any], path: str) -> bytes:
    manifest = validate_packet_tree_manifest(manifest)
    path = require_relative_file(path, "packet file lookup path")
    record = next((item for item in manifest["files"] if item["path"] == path), None)
    if record is None:
        raise ProtocolError(f"packet file is absent: {path}")
    if record["encoding"] == "UTF8":
        return record["content"].encode("utf-8")
    return base64.b64decode(record["content"], validate=True)


def packet_json_file(manifest: dict[str, Any], path: str) -> Any:
    return strict_json_loads(packet_file_bytes(manifest, path), f"packet file {path}")


def artifact_bytes(value: Any, label: str) -> bytes:
    if isinstance(value, bytes):
        return value
    if isinstance(value, Path):
        return value.read_bytes()
    if isinstance(value, (dict, list)):
        return canonical_json_bytes(value)
    raise ProtocolError(f"{label} must be bytes, a path, or a JSON object/array")


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


def validate_atom_manifest(
    value: Any,
    expected_mode: str | None = None,
    expected_status: str | None = None,
) -> dict[str, Any]:
    manifest = require_exact_keys(
        value, {"schema_version", "status", "mode", "atoms"}, "atom manifest"
    )
    if (
        manifest["schema_version"] != 1
        or manifest["status"] not in ("DRAFT", "READY")
        or (expected_status is not None and manifest["status"] != expected_status)
    ):
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


def validate_defect_rules(
    value: Any, expected_status: str | None = None
) -> dict[str, Any]:
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
    if (
        rules["schema_version"] != 1
        or rules["status"] not in ("DRAFT", "READY")
        or (expected_status is not None and rules["status"] != expected_status)
    ):
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


def expected_report_projection_contract(status: str = "DRAFT") -> dict[str, Any]:
    if status not in ("DRAFT", "READY"):
        raise ProtocolError("report projection contract expected status is invalid")
    return {
        "schema_version": 1,
        "status": status,
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


def validate_report_projection_contract(
    value: Any, expected_status: str = "DRAFT"
) -> dict[str, Any]:
    if value != expected_report_projection_contract(expected_status):
        raise ProtocolError(
            f"report projection contract is not the exact frozen {expected_status} contract"
        )
    return value


def derive_report_secret_inventory(
    static_root: Path,
    launch: dict[str, Any],
    lease: dict[str, Any],
    reviewed: dict[str, Any],
    packages_document: dict[str, Any],
    target_row: dict[str, Any],
) -> dict[str, Any]:
    """Build the complete finite nominal-secret inventory from bound provenance."""

    launch = validate_launch_record(launch)
    lease = validate_lease(lease)
    if (
        launch["role"] != "report"
        or lease["slot_id"] != launch["slot_id"]
        or launch != load_bound_launch(lease)
    ):
        raise ProtocolError("secret-inventory derivation requires one bound report lease")
    role = launch["condition_role"]
    packages = packages_document.get("packages")
    if not isinstance(packages, dict) or set(packages) != {"v5", "v4", "no_skill"}:
        raise ProtocolError("secret-inventory package document is not exact")

    tokens_by_value: dict[str, dict[str, Any]] = {}

    def add_token(category: str, value: Any, provenance: str, kind: str) -> None:
        if not isinstance(value, str) or len(value.encode("utf-8")) < 12:
            return
        if value.casefold() in {"v5", "v4", "no_skill", "condition"}:
            return
        token = {
            "category": category,
            "value": value,
            "provenance": provenance,
            "match_kind": kind,
        }
        prior = tokens_by_value.get(value)
        if prior is not None:
            if (
                prior["category"] != category
                or prior["match_kind"] != kind
            ):
                raise ProtocolError("derived report secret has conflicting category or type")
            return
        tokens_by_value[value] = token

    invocation = reviewed["invocation_blocks"][role]
    if invocation:
        add_token(
            "TREATMENT_INSTRUCTION_OR_PACKAGE_IDENTITY",
            invocation,
            f"static/integration/integration-values.json#invocation_blocks.{role}",
            "EXACT_MULTIWORD_TREATMENT_PHRASE",
        )
    package = packages[role]
    if package is not None:
        for field in ("byte_tree_sha256", "skill_sha256"):
            if field in package:
                add_token(
                    "TREATMENT_INSTRUCTION_OR_PACKAGE_IDENTITY",
                    package[field],
                    f"packages.json#packages.{role}.{field}",
                    "EXACT_HEX_DIGEST",
                )
        source_path = package.get("source_path")
        if isinstance(source_path, str):
            add_token(
                "TREATMENT_INSTRUCTION_OR_PACKAGE_IDENTITY",
                str(static_root / Path(*PurePosixPath(source_path).parts)),
                f"packages.json#packages.{role}.source_path",
                "EXACT_ABSOLUTE_PATH",
            )

    runtime_fields = {
        "launch.workspace_root": launch["workspace_root"],
        "launch.input_root": launch["input_root"],
        "launch.output_root": launch["output_root"],
        "launch.cell_id": launch["cell_id"],
        "launch.assignment_id": launch["assignment_id"],
        "launch.slot_id": launch["slot_id"],
        "launch.run_id": launch["run_id"],
        "launch.condition_label": launch["condition_label"],
        "launch.target_label": launch["target_label"],
        "launch.schedule_sha256": launch["schedule_sha256"],
        "launch.prompt_sha256": launch["prompt_sha256"],
        "launch.execution_manifest_sha256": launch["execution_manifest_sha256"],
        "launch.input_packet_sha256": launch["input_packet_sha256"],
        "launch.envelope_spec_sha256": launch["envelope_spec_sha256"],
        "lease.attempt_id": lease["attempt_id"],
        "lease.lease_token": lease["lease_token"],
        "lease.agent_id": lease["agent_id"],
        "lease.attempt_root": lease["attempt_root"],
    }
    for provenance, value in runtime_fields.items():
        if not isinstance(value, str):
            continue
        kind = (
            "EXACT_ABSOLUTE_PATH"
            if Path(value).is_absolute()
            else "EXACT_HEX_DIGEST"
            if HEX64.fullmatch(value)
            else "EXACT_UUID_OR_RUNTIME_ID"
        )
        category = (
            "REPORT_AGENT_IDENTITY"
            if provenance in {"lease.agent_id", "lease.attempt_id", "lease.lease_token"}
            else "CONDITION_BEARING_RUNTIME_IDENTIFIER"
        )
        add_token(category, value, provenance, kind)

    protected: set[str] = {
        str(value)
        for value in (
            launch["fixture_id"],
            launch["task_mode"],
            launch["target_path"],
            launch["authority_packet_path"],
            launch["target_byte_tree_sha256"],
            launch["authority_packet_sha256"],
            target_row.get("source_path"),
        )
        if isinstance(value, str) and value
    }
    source_path = target_row.get("source_path")
    if isinstance(source_path, str):
        target_root = static_root / Path(*PurePosixPath(source_path).parts)
        if target_root.is_dir() and not target_root.is_symlink():
            protected.update(
                path.relative_to(target_root).as_posix()
                for path in target_root.rglob("*")
                if path.is_file() and not path.is_symlink()
            )
    return {
        "schema_version": 1,
        "status": "READY",
        "builder_id": PROJECTION_INVENTORY_BUILDER_ID,
        "tokens": sorted(
            tokens_by_value.values(),
            key=lambda item: (
                item["value"], item["category"], item["provenance"], item["match_kind"]
            ),
        ),
        "protected_target_values": sorted(protected),
    }


def project_report_for_scorer(
    label: str, raw_report: bytes, secrets_inventory: dict[str, Any]
) -> tuple[bytes, dict[str, Any], dict[str, Any]]:
    if label not in LABELS or not isinstance(raw_report, bytes):
        raise ProtocolError("report projection label/raw bytes are invalid")
    inventory = require_exact_keys(
        secrets_inventory,
        {
            "schema_version",
            "status",
            "builder_id",
            "tokens",
            "protected_target_values",
        },
        "report projection secret inventory",
    )
    if (
        inventory["schema_version"] != 1
        or inventory["status"] != "READY"
        or inventory["builder_id"] != PROJECTION_INVENTORY_BUILDER_ID
    ):
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
            r"[A-Za-z0-9][A-Za-z0-9._:-]{15,}", secret["value"]
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


def build_score_input_packet(
    mode: str,
    scorer: str,
    labels_in_order: list[str],
    projected_reports: dict[str, bytes],
    leakage_receipts: dict[str, dict[str, Any]],
    atom_manifest: dict[str, Any],
    defect_rules: dict[str, Any],
    oracle_bytes: bytes,
    allowlist_bytes: bytes,
    evaluator_authority_bytes: bytes,
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest, mode)
    rules = validate_defect_rules(defect_rules)
    if scorer not in SCORERS:
        raise ProtocolError("score packet scorer is invalid")
    labels = require_labels(labels_in_order, "score input presentation order")
    if set(projected_reports) != set(LABELS) or set(leakage_receipts) != set(LABELS):
        raise ProtocolError("score packet projected report/receipt labels must be exactly A-O")
    files: dict[str, bytes] = {
        "resources/atom-manifest.json": canonical_json_bytes(manifest),
        "resources/defect-rules.json": canonical_json_bytes(rules),
        "resources/oracle.md": oracle_bytes,
        "resources/allowlist.txt": allowlist_bytes,
        "resources/evaluator-authority.json": evaluator_authority_bytes,
        "resources/presentation-order.json": canonical_json_bytes(labels),
    }
    reports: list[dict[str, Any]] = []
    projection_records: list[dict[str, Any]] = []
    for label in labels:
        report = projected_reports[label]
        receipt = validate_scorer_projection_receipt(
            leakage_receipts[label], label, sha256(report)
        )
        if not isinstance(report, bytes) or not isinstance(receipt, dict):
            raise ProtocolError("score packet report/receipt values have invalid types")
        receipt_bytes = canonical_json_bytes(receipt)
        report_path = f"reports/{label}.md"
        receipt_path = f"receipts/{label}.json"
        files[report_path] = report
        files[receipt_path] = receipt_bytes
        forced = receipt.get("redaction_present")
        if type(forced) is not bool:
            raise ProtocolError("leakage receipt must bind a boolean redaction_present")
        record = {
            "label": label,
            "projected_report_path": report_path,
            "projected_report_sha256": sha256(report),
            "leakage_receipt_path": receipt_path,
            "leakage_receipt_sha256": sha256(receipt_bytes),
            "gh12_forced_present": forced,
        }
        reports.append(record)
        projection_records.append(record)
    projection_bundle = canonical_json_bytes(projection_records)
    files["resources/projection-index.json"] = projection_bundle
    packet_tree = build_packet_tree_manifest(
        "SCORER-INPUT", f"{mode}-{scorer}-input", files
    )
    return {
        "schema_version": 1,
        "status": "SCORER-INPUT-PACKET",
        "mode": mode,
        "scorer_id": scorer,
        "input_digests": {
            "projection_bundle_sha256": sha256(projection_bundle),
            "atom_manifest_sha256": sha256(canonical_json_bytes(manifest)),
            "defect_rules_sha256": sha256(canonical_json_bytes(rules)),
            "oracle_sha256": sha256(oracle_bytes),
            "allowlist_sha256": sha256(allowlist_bytes),
            "evaluator_authority_sha256": sha256(evaluator_authority_bytes),
            "presentation_order_sha256": sha256(canonical_json_bytes(labels)),
        },
        "resource_paths": copy.deepcopy(SCORE_RESOURCE_PATHS),
        "labels_in_order": labels,
        "reports": reports,
        "packet_tree": packet_tree,
    }


def validate_scorer_projection_receipt(
    value: Any, expected_label: str, expected_report_sha256: str
) -> dict[str, Any]:
    receipt = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "label",
            "projected_report_sha256",
            "redaction_present",
            "replacement_count",
        },
        "scorer projection receipt",
    )
    if (
        receipt["schema_version"] != 1
        or receipt["status"] != "PROJECTED"
        or receipt["label"] != expected_label
        or receipt["projected_report_sha256"] != expected_report_sha256
        or type(receipt["redaction_present"]) is not bool
        or type(receipt["replacement_count"]) is not int
        or receipt["replacement_count"] < 0
        or receipt["redaction_present"] is not (receipt["replacement_count"] > 0)
    ):
        raise ProtocolError("scorer projection receipt is invalid or mismatched")
    return receipt


def validate_score_input_packet(value: Any, expected_mode: str, expected_scorer: str) -> dict[str, Any]:
    packet = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "mode",
            "scorer_id",
            "input_digests",
            "resource_paths",
            "labels_in_order",
            "reports",
            "packet_tree",
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
    resource_paths = require_exact_keys(
        packet["resource_paths"],
        {
            "projection_bundle",
            "atom_manifest",
            "defect_rules",
            "oracle",
            "allowlist",
            "evaluator_authority",
            "presentation_order",
        },
        "score input resource paths",
    )
    if resource_paths != SCORE_RESOURCE_PATHS:
        raise ProtocolError("score input resource paths are not the frozen exact paths")
    tree = validate_packet_tree_manifest(packet["packet_tree"], "SCORER-INPUT")
    if tree["packet_id"] != f"{expected_mode}-{expected_scorer}-input":
        raise ProtocolError("score packet tree identity mismatch")
    digest_fields = {
        "projection_bundle": "projection_bundle_sha256",
        "atom_manifest": "atom_manifest_sha256",
        "defect_rules": "defect_rules_sha256",
        "oracle": "oracle_sha256",
        "allowlist": "allowlist_sha256",
        "evaluator_authority": "evaluator_authority_sha256",
        "presentation_order": "presentation_order_sha256",
    }
    for role, path in resource_paths.items():
        path = require_relative_file(path, f"score input {role} path")
        if sha256(packet_file_bytes(tree, path)) != digests[digest_fields[role]]:
            raise ProtocolError(f"score input resource digest mismatch: {role}")
    labels = require_labels(packet["labels_in_order"], "score input presentation order")
    if strict_json_loads(
        packet_file_bytes(tree, resource_paths["presentation_order"]),
        "score presentation order",
    ) != labels:
        raise ProtocolError("score presentation-order bytes do not match labels_in_order")
    if not isinstance(packet["reports"], list):
        raise ProtocolError("score input packet reports must be a list")
    report_labels: list[str] = []
    for raw in packet["reports"]:
        report = require_exact_keys(
            raw,
            {
                "label",
                "projected_report_path",
                "projected_report_sha256",
                "leakage_receipt_path",
                "leakage_receipt_sha256",
                "gh12_forced_present",
            },
            "score input projected report",
        )
        if report["label"] not in LABELS or type(report["gh12_forced_present"]) is not bool:
            raise ProtocolError("score input projected report identity/flag is invalid")
        for field in ("projected_report_path", "leakage_receipt_path"):
            require_relative_file(report[field], f"score input {field}")
        for field in ("projected_report_sha256", "leakage_receipt_sha256"):
            if not isinstance(report[field], str) or not HEX64.fullmatch(report[field]):
                raise ProtocolError("score input projected report digest is invalid")
        report_bytes = packet_file_bytes(tree, report["projected_report_path"])
        receipt_bytes = packet_file_bytes(tree, report["leakage_receipt_path"])
        if (
            sha256(report_bytes) != report["projected_report_sha256"]
            or sha256(receipt_bytes) != report["leakage_receipt_sha256"]
        ):
            raise ProtocolError("score input report/receipt content binding mismatch")
        receipt = validate_scorer_projection_receipt(
            strict_json_loads(receipt_bytes, "score leakage receipt"),
            report["label"],
            report["projected_report_sha256"],
        )
        if receipt["redaction_present"] is not report["gh12_forced_present"]:
            raise ProtocolError("score leakage receipt does not bind its projected report")
        report_labels.append(report["label"])
    if report_labels != labels:
        raise ProtocolError("score input reports must exactly follow the frozen presentation order")
    expected_paths = set(SCORE_RESOURCE_PATHS.values()) | {
        f"reports/{label}.md" for label in LABELS
    } | {f"receipts/{label}.json" for label in LABELS}
    actual_paths = {record["path"] for record in tree["files"]}
    if actual_paths != expected_paths:
        raise ProtocolError("score packet tree path set is not exact")
    expected_index = canonical_json_bytes(packet["reports"])
    if packet_file_bytes(tree, SCORE_RESOURCE_PATHS["projection_bundle"]) != expected_index:
        raise ProtocolError("score projection index is not the canonical report index")
    return packet


def require_exact_score_input_packet(
    value: Any,
    expected: dict[str, Any],
    expected_mode: str,
    expected_scorer: str,
    *,
    raw_bytes: bytes | None = None,
) -> dict[str, Any]:
    packet = validate_score_input_packet(value, expected_mode, expected_scorer)
    expected = validate_score_input_packet(expected, expected_mode, expected_scorer)
    if packet != expected:
        raise ProtocolError("scorer input packet is not the exact deterministic derivation")
    if raw_bytes is not None and raw_bytes != canonical_json_bytes(expected):
        raise ProtocolError("scorer input packet bytes are not canonical deterministic bytes")
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
    evidence_packet: Any,
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest)
    first = validate_direct_score(first, manifest, defect_rules, "s1", first_input_packet)
    second = validate_direct_score(second, manifest, defect_rules, "s2", second_input_packet)
    evidence_bytes = artifact_bytes(evidence_packet, "consistency evidence packet")
    evidence_packet_sha256 = sha256(evidence_bytes)
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
    packet_tree = build_packet_tree_manifest(
        "CONSISTENCY-INPUT",
        f"{manifest['mode']}-consistency-input",
        {
            "scores/s1.json": canonical_json_bytes(first),
            "scores/s2.json": canonical_json_bytes(second),
            "score-inputs/s1.json": canonical_json_bytes(first_input_packet),
            "score-inputs/s2.json": canonical_json_bytes(second_input_packet),
            "resources/atom-manifest.json": canonical_json_bytes(manifest),
            "resources/defect-rules.json": canonical_json_bytes(
                validate_defect_rules(defect_rules)
            ),
            "resources/evidence-packet.bin": evidence_bytes,
        },
    )
    return {
        "schema_version": 1,
        "status": "CONSISTENCY-INPUT-PACKET",
        "mode": manifest["mode"],
        "input_digests": input_digests,
        "binding_sha256": sha256(canonical_json_bytes(input_digests)),
        "labels_in_order": list(LABELS),
        "novel_assertions": assertions,
        "packet_tree": packet_tree,
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
            "labels_in_order",
            "novel_assertions",
            "packet_tree",
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
    require_labels(packet["labels_in_order"], "consistency packet label order")
    tree = validate_packet_tree_manifest(packet["packet_tree"], "CONSISTENCY-INPUT")
    if tree["packet_id"] != f"{packet['mode']}-consistency-input":
        raise ProtocolError("consistency packet-tree identity mismatch")
    bound_files = {
        "score_s1_sha256": "scores/s1.json",
        "score_s2_sha256": "scores/s2.json",
        "atom_manifest_sha256": "resources/atom-manifest.json",
        "defect_rules_sha256": "resources/defect-rules.json",
        "evidence_packet_sha256": "resources/evidence-packet.bin",
    }
    for digest_field, path in bound_files.items():
        if sha256(packet_file_bytes(tree, path)) != digests[digest_field]:
            raise ProtocolError(f"consistency packet digest mismatch: {digest_field}")
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
    evidence_packet: Any,
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
        evidence_packet,
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
        "evidence_packet_sha256": sha256(
            artifact_bytes(evidence_packet, "adjudication evidence packet")
        ),
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
    packet_tree = build_packet_tree_manifest(
        "ADJUDICATION-INPUT",
        f"{mode}-adjudication-input",
        {
            "scores/s1.json": canonical_json_bytes(first),
            "scores/s2.json": canonical_json_bytes(second),
            "score-inputs/s1.json": canonical_json_bytes(first_input_packet),
            "score-inputs/s2.json": canonical_json_bytes(second_input_packet),
            "consistency/input.json": canonical_json_bytes(consistency_packet),
            "consistency/c1.json": canonical_json_bytes(consistency_first),
            "consistency/c2.json": canonical_json_bytes(consistency_second),
            "resources/atom-manifest.json": canonical_json_bytes(manifest),
            "resources/defect-rules.json": canonical_json_bytes(
                validate_defect_rules(defect_rules)
            ),
            "resources/evidence-packet.bin": artifact_bytes(
                evidence_packet, "adjudication evidence packet"
            ),
        },
    )
    return {
        "schema_version": 1,
        "status": "ADJUDICATION-PACKET",
        "mode": mode,
        "input_digests": input_digests,
        "binding_sha256": binding_sha256,
        "cells": records,
        "packet_tree": packet_tree,
    }


def validate_adjudication_packet(value: Any) -> dict[str, Any]:
    packet = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "mode",
            "input_digests",
            "binding_sha256",
            "cells",
            "packet_tree",
        },
        "adjudication packet",
    )
    if (
        packet["schema_version"] != 1
        or packet["status"] != "ADJUDICATION-PACKET"
        or packet["mode"] not in MODES
    ):
        raise ProtocolError("adjudication packet identity/status mismatch")
    digests = require_exact_keys(
        packet["input_digests"],
        {
            "score_s1_sha256",
            "score_s2_sha256",
            "consistency_c1_sha256",
            "consistency_c2_sha256",
            "consistency_packet_sha256",
            "atom_manifest_sha256",
            "defect_rules_sha256",
            "evidence_packet_sha256",
        },
        "adjudication packet input digests",
    )
    if any(not isinstance(item, str) or not HEX64.fullmatch(item) for item in digests.values()):
        raise ProtocolError("adjudication packet contains an invalid digest")
    if packet["binding_sha256"] != sha256(canonical_json_bytes(digests)):
        raise ProtocolError("adjudication packet binding mismatch")
    tree = validate_packet_tree_manifest(packet["packet_tree"], "ADJUDICATION-INPUT")
    if tree["packet_id"] != f"{packet['mode']}-adjudication-input":
        raise ProtocolError("adjudication packet-tree identity mismatch")
    file_bindings = {
        "score_s1_sha256": "scores/s1.json",
        "score_s2_sha256": "scores/s2.json",
        "consistency_c1_sha256": "consistency/c1.json",
        "consistency_c2_sha256": "consistency/c2.json",
        "consistency_packet_sha256": "consistency/input.json",
        "atom_manifest_sha256": "resources/atom-manifest.json",
        "defect_rules_sha256": "resources/defect-rules.json",
        "evidence_packet_sha256": "resources/evidence-packet.bin",
    }
    for digest_field, path in file_bindings.items():
        if sha256(packet_file_bytes(tree, path)) != digests[digest_field]:
            raise ProtocolError(f"adjudication packet file mismatch: {digest_field}")
    if not isinstance(packet["cells"], list):
        raise ProtocolError("adjudication packet cells must be a list")
    seen: set[str] = set()
    sort_keys: list[tuple[str, str]] = []
    for raw in packet["cells"]:
        cell = require_exact_keys(raw, {"cell_id", "label", "field", "reasons"}, "adjudication cell")
        if (
            not isinstance(cell["cell_id"], str)
            or re.fullmatch(r"[0-9a-f]{24}", cell["cell_id"]) is None
            or cell["cell_id"] in seen
            or cell["label"] not in LABELS
            or not isinstance(cell["field"], str)
            or not cell["field"]
            or not isinstance(cell["reasons"], list)
            or not cell["reasons"]
            or len(cell["reasons"]) != len(set(cell["reasons"]))
            or cell["reasons"] != sorted(cell["reasons"])
        ):
            raise ProtocolError("adjudication packet cell is invalid")
        seen.add(cell["cell_id"])
        sort_keys.append((cell["label"], cell["field"]))
    if sort_keys != sorted(sort_keys):
        raise ProtocolError("adjudication packet cells are not deterministically ordered")
    return packet


def validate_adjudication(value: Any, packet: dict[str, Any]) -> dict[str, Any]:
    packet = validate_adjudication_packet(packet)
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
    evidence_packet: Any,
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
        evidence_packet,
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
        evidence_packet,
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
        "adjudication_packet_sha256": sha256(canonical_json_bytes(packet)),
        "adjudication_sha256": (
            sha256(canonical_json_bytes(adjudication)) if adjudication is not None else None
        ),
        "reports": final_reports,
    }


def validate_final_score(
    value: Any, atom_manifest: dict[str, Any], defect_rules: dict[str, Any]
) -> dict[str, Any]:
    """Validate a merged mode score independently of the merge invocation."""

    manifest = validate_atom_manifest(atom_manifest)
    rules = validate_defect_rules(defect_rules)
    score = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "mode",
            "input_binding_sha256",
            "adjudication_packet_sha256",
            "adjudication_sha256",
            "reports",
        },
        "final score",
    )
    if (
        score["schema_version"] != 1
        or score["status"] != "FINAL-SCORE"
        or score["mode"] != manifest["mode"]
    ):
        raise ProtocolError("final-score identity/status mismatch")
    for field in ("input_binding_sha256", "adjudication_packet_sha256"):
        if not isinstance(score[field], str) or not HEX64.fullmatch(score[field]):
            raise ProtocolError(f"final score contains an invalid digest: {field}")
    if score["adjudication_sha256"] is not None and (
        not isinstance(score["adjudication_sha256"], str)
        or not HEX64.fullmatch(score["adjudication_sha256"])
    ):
        raise ProtocolError("final score contains an invalid adjudication digest")
    if not isinstance(score["reports"], list):
        raise ProtocolError("final score reports must be a list")
    labels: list[str] = []
    atom_ids = [atom["id"] for atom in manifest["atoms"]]
    expected_hard = hard_error_ids(rules, manifest["mode"])
    expected_global = global_defect_ids(rules)
    for raw in score["reports"]:
        report = require_exact_keys(
            raw,
            {"label", "atoms", "hard_errors", "global_defects", "novel_findings"},
            "final-score report",
        )
        if report["label"] not in LABELS:
            raise ProtocolError("final-score report label is invalid")
        labels.append(report["label"])
        if not isinstance(report["atoms"], list):
            raise ProtocolError("final-score atoms must be a list")
        direct: dict[str, str] = {}
        observed_atoms: list[str] = []
        for raw_atom in report["atoms"]:
            atom = require_exact_keys(
                raw_atom,
                {
                    "id",
                    "direct_decision",
                    "blocked_by",
                    "certificate_decision",
                    "root_failures",
                },
                "final-score atom",
            )
            if atom["direct_decision"] not in ("PASS", "FAIL"):
                raise ProtocolError("final-score direct atom decision is invalid")
            observed_atoms.append(atom["id"])
            direct[atom["id"]] = atom["direct_decision"]
        if observed_atoms != atom_ids:
            raise ProtocolError("final score must list every atom in manifest order")
        recomputed = compute_atom_certificates(manifest, direct)["atoms"]
        if report["atoms"] != recomputed:
            raise ProtocolError("final-score atom certificates are not recomputable")
        for field, expected in (
            ("hard_errors", expected_hard),
            ("global_defects", expected_global),
        ):
            observed = report[field]
            if (
                not isinstance(observed, list)
                or len(observed) != len(set(observed))
                or observed != [rule_id for rule_id in expected if rule_id in observed]
            ):
                raise ProtocolError(f"final-score {field} is not an ordered rule subset")
        novel_ids: list[str] = []
        if not isinstance(report["novel_findings"], list):
            raise ProtocolError("final-score novel findings must be a list")
        for raw_finding in report["novel_findings"]:
            finding = require_exact_keys(
                raw_finding, {"id", "classification", "sources"}, "final novel finding"
            )
            if (
                not isinstance(finding["id"], str)
                or re.fullmatch(r"N-[0-9a-f]{24}", finding["id"]) is None
                or finding["classification"] not in NOVEL_CATEGORIES
                or not isinstance(finding["sources"], list)
                or not finding["sources"]
            ):
                raise ProtocolError("final novel finding is invalid")
            source_keys: list[tuple[str, str]] = []
            for raw_source in finding["sources"]:
                source = require_exact_keys(
                    raw_source, {"scorer_id", "source_id"}, "final novel source"
                )
                if (
                    source["scorer_id"] not in SCORERS
                    or not isinstance(source["source_id"], str)
                    or re.fullmatch(r"s[12]-N[1-9][0-9]*", source["source_id"])
                    is None
                    or not source["source_id"].startswith(source["scorer_id"] + "-")
                ):
                    raise ProtocolError("final novel source is invalid")
                source_keys.append((source["scorer_id"], source["source_id"]))
            if source_keys != sorted(source_keys) or len(source_keys) != len(
                set(source_keys)
            ):
                raise ProtocolError("final novel sources are not unique and sorted")
            novel_ids.append(finding["id"])
        if len(novel_ids) != len(set(novel_ids)):
            raise ProtocolError("final-score novel finding IDs are duplicated")
    if labels != list(LABELS):
        raise ProtocolError("final score must contain A through O in canonical order")
    return score


def validate_scoring_bundle_manifest(value: Any) -> dict[str, Any]:
    bundle = require_exact_keys(
        value, {"schema_version", "status", "modes"}, "scoring bundle manifest"
    )
    if (
        bundle["schema_version"] != 1
        or bundle["status"] != "BOUND"
        or not isinstance(bundle["modes"], list)
    ):
        raise ProtocolError("scoring bundle identity/status mismatch")
    observed_modes: list[str] = []
    digest_fields = {
        "consistency_input_packet_digest",
        "adjudication_packet_digest",
        "final_score_digest",
    }
    pair_fields = {
        "score_input_packet_digests",
        "direct_score_digests",
        "consistency_review_digests",
        "scorer_launch_envelope_digests",
        "consistency_launch_envelope_digests",
    }
    nullable_fields = {"adjudication_digest", "adjudicator_launch_envelope_digest"}
    for raw in bundle["modes"]:
        row = require_exact_keys(
            raw,
            {"mode", *digest_fields, *pair_fields, *nullable_fields},
            "scoring bundle mode",
        )
        if row["mode"] not in MODES:
            raise ProtocolError("scoring bundle mode is invalid")
        observed_modes.append(row["mode"])
        for field in digest_fields:
            if not isinstance(row[field], str) or not HEX64.fullmatch(row[field]):
                raise ProtocolError(f"scoring bundle digest is invalid: {field}")
        for field in pair_fields:
            pair = row[field]
            if (
                not isinstance(pair, list)
                or len(pair) != 2
                or any(not isinstance(item, str) or not HEX64.fullmatch(item) for item in pair)
            ):
                raise ProtocolError(f"scoring bundle digest pair is invalid: {field}")
        for field in nullable_fields:
            if row[field] is not None and (
                not isinstance(row[field], str) or not HEX64.fullmatch(row[field])
            ):
                raise ProtocolError(f"scoring bundle nullable digest is invalid: {field}")
        if (row["adjudication_digest"] is None) != (
            row["adjudicator_launch_envelope_digest"] is None
        ):
            raise ProtocolError("scoring bundle adjudication/envelope nullability differs")
    if observed_modes != list(MODES):
        raise ProtocolError("scoring bundle must contain every mode in canonical order")
    return bundle


def validate_integration_hooks(
    value: Any, expected_status: str = "DRAFT"
) -> dict[str, Any]:
    hooks = require_exact_keys(
        value,
        {"schema_version", "status", "blocking", "failure_gate", "hooks"},
        "integration hooks",
    )
    if (
        hooks["schema_version"] != 1
        or expected_status not in ("DRAFT", "READY")
        or hooks["status"] != expected_status
        or hooks["blocking"] is not True
        or hooks["failure_gate"] != "D-STATIC-INTEGRITY"
        or not isinstance(hooks["hooks"], list)
    ):
        raise ProtocolError(
            f"integration hooks must be the blocking schema-v1 {expected_status} inventory"
        )
    seen: list[str] = []
    for index, raw in enumerate(hooks["hooks"]):
        hook = require_exact_keys(
            raw,
            {"id", "phase", "required", "implementation_status", "consumes", "produces"},
            f"integration hook {index}",
        )
        if (
            not isinstance(hook["id"], str)
            or hook["required"] is not True
            or hook["phase"] not in INTEGRATION_PHASES
            or hook["phase"] != INTEGRATION_HOOK_PHASES.get(hook["id"])
            or hook["implementation_status"]
            != (
                "DIRECTLY_REVALIDATED"
                if hook["phase"] in ("SNAPSHOT_BUILD", "FINALIZE_STATIC")
                else "INDEPENDENT_RECEIPT_REQUIRED"
                if hook["phase"] == "SNAPSHOT_REVIEW"
                else "RUNTIME_RECEIPT_REQUIRED"
            )
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


def validate_integration_receipt(
    value: Any, expected_hook_id: str, expected_phase: str
) -> dict[str, Any]:
    if (
        expected_hook_id not in INTEGRATION_HOOK_PHASES
        or expected_phase != INTEGRATION_HOOK_PHASES[expected_hook_id]
    ):
        raise ProtocolError("integration receipt expected hook/phase is invalid")
    try:
        validator = trusted_integration_module()["validate_integration_receipt"]
        return validator(
            value,
            expected_hook_id=expected_hook_id,
            expected_phase=expected_phase,
        )
    except Exception as error:
        raise ProtocolError("integration receipt identity/content is invalid") from error


def validate_control_manifest(
    value: Any,
    expected_status: str = "DRAFT",
    atom_root: Path | None = None,
) -> dict[str, Any]:
    manifest = require_exact_keys(
        value, {"schema_version", "status", "controls"}, "control manifest"
    )
    if expected_status not in ("DRAFT", "READY"):
        raise ProtocolError("control manifest expected status is invalid")
    if manifest["schema_version"] != 1 or manifest["status"] != expected_status:
        raise ProtocolError(f"control manifest must be schema-v1 {expected_status}")
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
    atoms_directory = atom_root or (RUN / "freeze" / "atoms")
    atom_modes = {
        atom["id"]: mode
        for mode in MODES
        for atom in validate_atom_manifest(
            read_json(atoms_directory / f"{mode}.json"), mode, expected_status
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


def validate_materiality_contract(
    value: Any, expected_status: str = "DRAFT"
) -> dict[str, Any]:
    if expected_status not in ("DRAFT", "READY"):
        raise ProtocolError("materiality-review contract expected status is invalid")
    expected = {
        "schema_version": 1,
        "status": expected_status,
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
        raise ProtocolError(
            f"materiality-review contract is not the exact frozen {expected_status} contract"
        )
    return value


def normalize_materiality_description(value: Any) -> str:
    if not isinstance(value, str):
        raise ProtocolError("materiality description must be text")
    normalized = " ".join(unicodedata.normalize("NFKC", value).split()).casefold()
    if not normalized:
        raise ProtocolError("materiality description must be nonblank")
    return normalized


def build_materiality_review_packet(
    scope_payloads: dict[str, Any],
    materiality_contract: dict[str, Any] | None = None,
    expected_contract_status: str = "DRAFT",
) -> dict[str, Any]:
    """Build the byte-identical packet supplied independently to m1 and m2."""

    if not isinstance(scope_payloads, dict) or set(scope_payloads) != set(
        MATERIALITY_SCOPES
    ):
        raise ProtocolError("materiality packet scopes must be the exact frozen scope")
    files: dict[str, bytes] = {
        "resources/materiality-review-contract.json": canonical_json_bytes(
            validate_materiality_contract(
                materiality_contract
                if materiality_contract is not None
                else read_json(RUN / "materiality-review-contract.json"),
                expected_contract_status,
            )
        )
    }
    scope_records: list[dict[str, Any]] = []
    for index, scope in enumerate(MATERIALITY_SCOPES, start=1):
        data = artifact_bytes(scope_payloads[scope], f"materiality scope {scope}")
        path = f"scopes/{index:02d}-{scope.lower().replace('_', '-')}.bin"
        files[path] = data
        scope_records.append(
            {"scope": scope, "path": path, "size": len(data), "sha256": sha256(data)}
        )
    tree = build_packet_tree_manifest(
        "MATERIALITY-REVIEW-INPUT", "materiality-review-input", files
    )
    return {
        "schema_version": 1,
        "status": "MATERIALITY-REVIEW-PACKET",
        "reviewer_ids": list(MATERIALITY_REVIEWERS),
        "scopes_in_order": list(MATERIALITY_SCOPES),
        "scope_payloads": scope_records,
        "packet_tree": tree,
    }


def validate_materiality_review_packet(
    value: Any, expected_contract_status: str = "DRAFT"
) -> dict[str, Any]:
    packet = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "reviewer_ids",
            "scopes_in_order",
            "scope_payloads",
            "packet_tree",
        },
        "materiality review packet",
    )
    if (
        packet["schema_version"] != 1
        or packet["status"] != "MATERIALITY-REVIEW-PACKET"
        or packet["reviewer_ids"] != list(MATERIALITY_REVIEWERS)
        or packet["scopes_in_order"] != list(MATERIALITY_SCOPES)
    ):
        raise ProtocolError("materiality review packet identity/scope mismatch")
    tree = validate_packet_tree_manifest(
        packet["packet_tree"], "MATERIALITY-REVIEW-INPUT"
    )
    if tree["packet_id"] != "materiality-review-input":
        raise ProtocolError("materiality review packet-tree identity mismatch")
    contract_path = "resources/materiality-review-contract.json"
    validate_materiality_contract(
        packet_json_file(tree, contract_path), expected_contract_status
    )
    if not isinstance(packet["scope_payloads"], list):
        raise ProtocolError("materiality packet scope payloads must be a list")
    scopes: list[str] = []
    paths: list[str] = []
    for raw in packet["scope_payloads"]:
        record = require_exact_keys(
            raw, {"scope", "path", "size", "sha256"}, "materiality scope payload"
        )
        if (
            record["scope"] not in MATERIALITY_SCOPES
            or type(record["size"]) is not int
            or record["size"] < 0
            or not isinstance(record["sha256"], str)
            or not HEX64.fullmatch(record["sha256"])
        ):
            raise ProtocolError("materiality scope payload metadata is invalid")
        path = require_relative_file(record["path"], "materiality scope payload path")
        data = packet_file_bytes(tree, path)
        if len(data) != record["size"] or sha256(data) != record["sha256"]:
            raise ProtocolError("materiality scope payload content binding mismatch")
        scopes.append(record["scope"])
        paths.append(path)
    if scopes != list(MATERIALITY_SCOPES) or len(paths) != len(set(paths)):
        raise ProtocolError("materiality scope payloads are not exact and ordered")
    tree_paths = {item["path"] for item in tree["files"]}
    if tree_paths != {contract_path, *paths}:
        raise ProtocolError("materiality packet tree contains an unexpected file")
    return packet


def validate_materiality_review(
    value: Any,
    input_packet: dict[str, Any],
    expected_reviewer: str | None = None,
    expected_contract_status: str = "DRAFT",
) -> dict[str, Any]:
    packet = validate_materiality_review_packet(
        input_packet, expected_contract_status
    )
    review = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "reviewer_id",
            "input_packet_sha256",
            "scope_attestations",
            "findings",
        },
        "materiality review",
    )
    reviewer = review["reviewer_id"]
    if (
        review["schema_version"] != 1
        or review["status"] != "MATERIALITY-REVIEW"
        or reviewer not in MATERIALITY_REVIEWERS
        or (expected_reviewer is not None and reviewer != expected_reviewer)
        or review["input_packet_sha256"] != sha256(canonical_json_bytes(packet))
    ):
        raise ProtocolError("materiality review identity/input binding mismatch")
    if not isinstance(review["scope_attestations"], list):
        raise ProtocolError("materiality scope attestations must be a list")
    attested: list[str] = []
    for raw in review["scope_attestations"]:
        attestation = require_exact_keys(
            raw, {"scope", "complete", "evidence"}, "materiality scope attestation"
        )
        if attestation["scope"] not in MATERIALITY_SCOPES or attestation["complete"] is not True:
            raise ProtocolError("materiality scope attestation is incomplete")
        validate_evidence(attestation["evidence"], "materiality scope attestation")
        attested.append(attestation["scope"])
    if attested != list(MATERIALITY_SCOPES):
        raise ProtocolError("materiality review must attest every scope in frozen order")
    if not isinstance(review["findings"], list):
        raise ProtocolError("materiality findings must be a list")
    ids: list[str] = []
    normalized_keys: list[tuple[str, str]] = []
    for raw in review["findings"]:
        finding = require_exact_keys(
            raw,
            {"id", "scope", "description", "evidence", "proposed_blocking"},
            "materiality finding",
        )
        if (
            not isinstance(finding["id"], str)
            or re.fullmatch(rf"{reviewer}-F[1-9][0-9]*", finding["id"]) is None
            or finding["scope"] not in MATERIALITY_SCOPES
            or type(finding["proposed_blocking"]) is not bool
        ):
            raise ProtocolError("materiality finding identity/scope/decision is invalid")
        normalized = normalize_materiality_description(finding["description"])
        validate_evidence(finding["evidence"], "materiality finding evidence")
        ids.append(finding["id"])
        normalized_keys.append((finding["scope"], normalized))
    if len(ids) != len(set(ids)) or len(normalized_keys) != len(set(normalized_keys)):
        raise ProtocolError("materiality finding identities/content must be unique per review")
    return review


def _materiality_union(
    first: dict[str, Any], second: dict[str, Any]
) -> list[dict[str, Any]]:
    grouped: dict[tuple[str, str], list[dict[str, Any]]] = {}
    for review in (first, second):
        for finding in review["findings"]:
            key = (
                finding["scope"],
                normalize_materiality_description(finding["description"]),
            )
            grouped.setdefault(key, []).append(
                {
                    "reviewer_id": review["reviewer_id"],
                    "source_id": finding["id"],
                    "description": finding["description"],
                    "evidence": finding["evidence"],
                    "decision": (
                        "BLOCKING" if finding["proposed_blocking"] else "NOT_BLOCKING"
                    ),
                }
            )
    union: list[dict[str, Any]] = []
    for (scope, normalized), sources in sorted(grouped.items()):
        finding_id = "M-" + sha256(
            f"v5-diagnostic-materiality-v1\0{scope}\0{normalized}".encode("utf-8")
        )[:24]
        union.append(
            {
                "finding_id": finding_id,
                "scope": scope,
                "normalized_description": normalized,
                "sources": sorted(
                    sources, key=lambda item: (item["reviewer_id"], item["source_id"])
                ),
            }
        )
    return union


def build_materiality_adjudication_packet(
    review_packet: dict[str, Any],
    review_m1: dict[str, Any],
    review_m2: dict[str, Any],
    expected_contract_status: str = "DRAFT",
) -> dict[str, Any]:
    review_packet = validate_materiality_review_packet(
        review_packet, expected_contract_status
    )
    review_m1 = validate_materiality_review(
        review_m1, review_packet, "m1", expected_contract_status
    )
    review_m2 = validate_materiality_review(
        review_m2, review_packet, "m2", expected_contract_status
    )
    union = _materiality_union(review_m1, review_m2)
    input_digests = {
        "review_packet_sha256": sha256(canonical_json_bytes(review_packet)),
        "review_m1_sha256": sha256(canonical_json_bytes(review_m1)),
        "review_m2_sha256": sha256(canonical_json_bytes(review_m2)),
    }
    binding = sha256(canonical_json_bytes(input_digests))
    cells: list[dict[str, Any]] = []
    for finding in union:
        reviewers = {item["reviewer_id"] for item in finding["sources"]}
        decisions = {item["decision"] for item in finding["sources"]}
        reasons: list[str] = []
        if reviewers != set(MATERIALITY_REVIEWERS):
            reasons.append("SINGLE_REVIEWER_FINDING")
        if len(decisions) != 1:
            reasons.append("REVIEWER_DISAGREEMENT")
        if reasons:
            cell_id = sha256(
                f"v5-diagnostic-materiality-cell-v1\0{binding}\0{finding['finding_id']}".encode(
                    "utf-8"
                )
            )[:24]
            cells.append(
                {
                    "cell_id": cell_id,
                    "finding_id": finding["finding_id"],
                    "scope": finding["scope"],
                    "normalized_description": finding["normalized_description"],
                    "source_ids": [item["source_id"] for item in finding["sources"]],
                    "proposed_decisions": [
                        {
                            "reviewer_id": item["reviewer_id"],
                            "source_id": item["source_id"],
                            "decision": item["decision"],
                        }
                        for item in finding["sources"]
                    ],
                    "reasons": reasons,
                }
            )
    tree = build_packet_tree_manifest(
        "MATERIALITY-ADJUDICATION-INPUT",
        "materiality-adjudication-input",
        {
            "review-input/packet.json": canonical_json_bytes(review_packet),
            "reviews/m1.json": canonical_json_bytes(review_m1),
            "reviews/m2.json": canonical_json_bytes(review_m2),
            "union/findings.json": canonical_json_bytes(union),
        },
    )
    return {
        "schema_version": 1,
        "status": "MATERIALITY-ADJUDICATION-PACKET",
        "input_digests": input_digests,
        "binding_sha256": binding,
        "union_findings": union,
        "cells": cells,
        "packet_tree": tree,
    }


def validate_materiality_adjudication_packet(
    value: Any, expected_contract_status: str = "DRAFT"
) -> dict[str, Any]:
    packet = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "input_digests",
            "binding_sha256",
            "union_findings",
            "cells",
            "packet_tree",
        },
        "materiality adjudication packet",
    )
    if packet["schema_version"] != 1 or packet["status"] != "MATERIALITY-ADJUDICATION-PACKET":
        raise ProtocolError("materiality adjudication packet identity/status mismatch")
    digests = require_exact_keys(
        packet["input_digests"],
        {"review_packet_sha256", "review_m1_sha256", "review_m2_sha256"},
        "materiality adjudication input digests",
    )
    if any(not isinstance(item, str) or not HEX64.fullmatch(item) for item in digests.values()):
        raise ProtocolError("materiality adjudication input digest is invalid")
    if packet["binding_sha256"] != sha256(canonical_json_bytes(digests)):
        raise ProtocolError("materiality adjudication binding mismatch")
    tree = validate_packet_tree_manifest(
        packet["packet_tree"], "MATERIALITY-ADJUDICATION-INPUT"
    )
    if tree["packet_id"] != "materiality-adjudication-input":
        raise ProtocolError("materiality adjudication packet-tree identity mismatch")
    review_packet = packet_json_file(tree, "review-input/packet.json")
    review_m1 = packet_json_file(tree, "reviews/m1.json")
    review_m2 = packet_json_file(tree, "reviews/m2.json")
    if (
        sha256(canonical_json_bytes(review_packet)) != digests["review_packet_sha256"]
        or sha256(canonical_json_bytes(review_m1)) != digests["review_m1_sha256"]
        or sha256(canonical_json_bytes(review_m2)) != digests["review_m2_sha256"]
    ):
        raise ProtocolError("materiality adjudication embedded review digest mismatch")
    validate_materiality_review_packet(review_packet, expected_contract_status)
    validate_materiality_review(
        review_m1, review_packet, "m1", expected_contract_status
    )
    validate_materiality_review(
        review_m2, review_packet, "m2", expected_contract_status
    )
    expected = build_materiality_adjudication_packet(
        review_packet, review_m1, review_m2, expected_contract_status
    )
    if packet != expected:
        raise ProtocolError("materiality adjudication packet is not deterministic")
    return packet


def validate_materiality_adjudication(
    value: Any,
    packet: dict[str, Any],
    expected_contract_status: str = "DRAFT",
) -> dict[str, Any]:
    packet = validate_materiality_adjudication_packet(
        packet, expected_contract_status
    )
    adjudication = require_exact_keys(
        value, {"schema_version", "status", "packet_sha256", "resolutions"},
        "materiality adjudication",
    )
    if (
        adjudication["schema_version"] != 1
        or adjudication["status"] != "ADJUDICATED"
        or adjudication["packet_sha256"] != sha256(canonical_json_bytes(packet))
        or not isinstance(adjudication["resolutions"], list)
    ):
        raise ProtocolError("materiality adjudication identity/input binding mismatch")
    by_cell = {item["cell_id"]: item for item in packet["cells"]}
    seen: list[str] = []
    for raw in adjudication["resolutions"]:
        resolution = require_exact_keys(
            raw, {"cell_id", "decision", "evidence"}, "materiality resolution"
        )
        if resolution["cell_id"] not in by_cell or resolution["decision"] not in (
            "BLOCKING",
            "NOT_BLOCKING",
        ):
            raise ProtocolError("materiality resolution cell/decision mismatch")
        validate_evidence(resolution["evidence"], "materiality resolution evidence")
        seen.append(resolution["cell_id"])
    if seen != [item["cell_id"] for item in packet["cells"]]:
        raise ProtocolError("materiality adjudication must resolve every cell once in order")
    return adjudication


def merge_materiality_ledger(
    review_packet: dict[str, Any],
    review_m1: dict[str, Any],
    review_m2: dict[str, Any],
    adjudication: dict[str, Any] | None,
    expected_contract_status: str = "DRAFT",
) -> dict[str, Any]:
    packet = build_materiality_adjudication_packet(
        review_packet, review_m1, review_m2, expected_contract_status
    )
    if packet["cells"]:
        if adjudication is None:
            raise ProtocolError("materiality disagreements require independent adjudication")
        adjudication = validate_materiality_adjudication(
            adjudication, packet, expected_contract_status
        )
        decisions = {
            item["cell_id"]: item["decision"] for item in adjudication["resolutions"]
        }
    else:
        if adjudication is not None:
            raise ProtocolError("empty materiality adjudication packet forbids an output")
        decisions = {}
    cell_by_finding = {item["finding_id"]: item for item in packet["cells"]}
    findings: list[dict[str, Any]] = []
    for finding in packet["union_findings"]:
        cell = cell_by_finding.get(finding["finding_id"])
        if cell is None:
            source_decisions = {item["decision"] for item in finding["sources"]}
            if len(source_decisions) != 1:
                raise ProtocolError("unrouted materiality disagreement")
            decision = next(iter(source_decisions))
            resolution = "AGREED"
        else:
            decision = decisions[cell["cell_id"]]
            resolution = "ADJUDICATED"
        findings.append(
            {
                "finding_id": finding["finding_id"],
                "scope": finding["scope"],
                "normalized_description": finding["normalized_description"],
                "blocking": decision == "BLOCKING",
                "resolution": resolution,
                "sources": [item["source_id"] for item in finding["sources"]],
            }
        )
    return {
        "schema_version": 1,
        "status": "COMPLETE",
        "input_digests": {
            "review_packet_sha256": packet["input_digests"]["review_packet_sha256"],
            "review_m1_sha256": packet["input_digests"]["review_m1_sha256"],
            "review_m2_sha256": packet["input_digests"]["review_m2_sha256"],
            "adjudication_packet_sha256": sha256(canonical_json_bytes(packet)),
            "adjudication_sha256": (
                sha256(canonical_json_bytes(adjudication))
                if adjudication is not None
                else None
            ),
        },
        "completed_reviewer_ids": list(MATERIALITY_REVIEWERS),
        "scope_complete": True,
        "findings": findings,
    }


def validate_materiality_ledger(value: Any) -> dict[str, Any]:
    ledger = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "input_digests",
            "completed_reviewer_ids",
            "scope_complete",
            "findings",
        },
        "materiality ledger",
    )
    if (
        ledger["schema_version"] != 1
        or ledger["status"] != "COMPLETE"
        or ledger["completed_reviewer_ids"] != list(MATERIALITY_REVIEWERS)
        or ledger["scope_complete"] is not True
    ):
        raise ProtocolError("materiality ledger identity/completeness mismatch")
    digests = require_exact_keys(
        ledger["input_digests"],
        {
            "review_packet_sha256",
            "review_m1_sha256",
            "review_m2_sha256",
            "adjudication_packet_sha256",
            "adjudication_sha256",
        },
        "materiality ledger input digests",
    )
    for field, digest in digests.items():
        if field == "adjudication_sha256" and digest is None:
            continue
        if not isinstance(digest, str) or not HEX64.fullmatch(digest):
            raise ProtocolError(f"materiality ledger digest is invalid: {field}")
    if not isinstance(ledger["findings"], list):
        raise ProtocolError("materiality ledger findings must be a list")
    finding_ids: list[str] = []
    for raw in ledger["findings"]:
        finding = require_exact_keys(
            raw,
            {
                "finding_id",
                "scope",
                "normalized_description",
                "blocking",
                "resolution",
                "sources",
            },
            "materiality ledger finding",
        )
        if (
            not isinstance(finding["finding_id"], str)
            or re.fullmatch(r"M-[0-9a-f]{24}", finding["finding_id"]) is None
            or finding["scope"] not in MATERIALITY_SCOPES
            or not isinstance(finding["normalized_description"], str)
            or normalize_materiality_description(finding["normalized_description"])
            != finding["normalized_description"]
            or type(finding["blocking"]) is not bool
            or finding["resolution"] not in ("AGREED", "ADJUDICATED")
            or not isinstance(finding["sources"], list)
            or not finding["sources"]
            or finding["sources"] != sorted(finding["sources"])
            or len(finding["sources"]) != len(set(finding["sources"]))
            or any(
                not isinstance(source, str)
                or re.fullmatch(r"m[12]-F[1-9][0-9]*", source) is None
                for source in finding["sources"]
            )
        ):
            raise ProtocolError("materiality ledger finding is invalid")
        finding_ids.append(finding["finding_id"])
    if finding_ids != sorted(finding_ids) or len(finding_ids) != len(set(finding_ids)):
        raise ProtocolError("materiality ledger findings are not unique and sorted")
    return ledger


def validate_word_count_manifest(value: Any) -> dict[str, Any]:
    manifest = require_exact_keys(
        value,
        {"schema_version", "status", "algorithm_id", "records"},
        "word-count manifest",
    )
    if (
        manifest["schema_version"] != 1
        or manifest["status"] != "COMPLETE"
        or manifest["algorithm_id"] != "unicode-whitespace-runs-python-v1"
        or not isinstance(manifest["records"], list)
    ):
        raise ProtocolError("word-count manifest identity/status mismatch")
    run_ids: list[str] = []
    for raw in manifest["records"]:
        record = require_exact_keys(raw, {"run_id", "receipt"}, "word-count record")
        if (
            not isinstance(record["run_id"], str)
            or REPORT_RUN_ID.fullmatch(record["run_id"]) is None
        ):
            raise ProtocolError("word-count record has an invalid run ID")
        receipt = require_exact_keys(
            record["receipt"],
            {
                "schema_version",
                "status",
                "algorithm_id",
                "report_sha256",
                "word_count",
                "word_cap",
                "valid",
            },
            "word-count receipt",
        )
        if (
            receipt["schema_version"] != 1
            or receipt["status"] != "COUNTED"
            or receipt["algorithm_id"] != manifest["algorithm_id"]
            or not isinstance(receipt["report_sha256"], str)
            or not HEX64.fullmatch(receipt["report_sha256"])
            or type(receipt["word_count"]) is not int
            or receipt["word_count"] < 0
            or type(receipt["word_cap"]) is not int
            or receipt["word_cap"] < 1
            or type(receipt["valid"]) is not bool
            or receipt["valid"]
            is not (receipt["word_count"] <= receipt["word_cap"])
        ):
            raise ProtocolError("word-count receipt is invalid")
        run_ids.append(record["run_id"])
    expected = [f"r{index:03d}" for index in range(1, 121)]
    if run_ids != expected:
        raise ProtocolError("word-count manifest must contain exactly r001 through r120")
    return manifest


def validate_projection_audit_manifest(value: Any) -> dict[str, Any]:
    manifest = require_exact_keys(
        value,
        {"schema_version", "status", "records"},
        "projection audit manifest",
    )
    if (
        manifest["schema_version"] != 1
        or manifest["status"] != "COMPLETE"
        or not isinstance(manifest["records"], list)
    ):
        raise ProtocolError("projection audit manifest identity/status mismatch")
    run_ids: list[str] = []
    mode_labels: list[tuple[str, str]] = []
    for raw in manifest["records"]:
        record = require_exact_keys(
            raw,
            {
                "run_id",
                "mode",
                "label",
                "secret_inventory_sha256",
                "secret_inventory",
                "receipt_sha256",
                "receipt",
            },
            "projection audit record",
        )
        if (
            not isinstance(record["run_id"], str)
            or REPORT_RUN_ID.fullmatch(record["run_id"]) is None
            or record["mode"] not in MODES
            or record["label"] not in LABELS
            or not isinstance(record["secret_inventory_sha256"], str)
            or not HEX64.fullmatch(record["secret_inventory_sha256"])
            or not isinstance(record["receipt_sha256"], str)
            or not HEX64.fullmatch(record["receipt_sha256"])
        ):
            raise ProtocolError("projection audit record identity is invalid")
        inventory = require_exact_keys(
            record["secret_inventory"],
            {
                "schema_version",
                "status",
                "builder_id",
                "tokens",
                "protected_target_values",
            },
            "projection secret inventory",
        )
        if (
            inventory["schema_version"] != 1
            or inventory["status"] != "READY"
            or inventory["builder_id"] != PROJECTION_INVENTORY_BUILDER_ID
            or not isinstance(inventory["tokens"], list)
            or not isinstance(inventory["protected_target_values"], list)
            or record["secret_inventory_sha256"]
            != sha256(canonical_json_bytes(inventory))
        ):
            raise ProtocolError("projection secret inventory is invalid or unbound")
        receipt = require_exact_keys(
            record["receipt"],
            {
                "schema_version",
                "status",
                "label",
                "raw_report_sha256",
                "projected_report_sha256",
                "replacements",
            },
            "projection audit receipt",
        )
        if (
            receipt["schema_version"] != 1
            or receipt["status"] != "EVALUATOR-ONLY-AUDIT"
            or receipt["label"] != record["label"]
            or any(
                not isinstance(receipt[field], str)
                or not HEX64.fullmatch(receipt[field])
                for field in ("raw_report_sha256", "projected_report_sha256")
            )
            or record["receipt_sha256"] != sha256(canonical_json_bytes(receipt))
            or not isinstance(receipt["replacements"], list)
        ):
            raise ProtocolError("projection audit receipt identity/binding is invalid")
        prior_end = -1
        for raw_replacement in receipt["replacements"]:
            replacement = require_exact_keys(
                raw_replacement,
                {
                    "category",
                    "offset",
                    "length",
                    "secret_sha256",
                    "placeholder",
                },
                "projection audit replacement",
            )
            if (
                replacement["category"] not in REPORT_SECRET_CATEGORIES
                or type(replacement["offset"]) is not int
                or replacement["offset"] < 0
                or type(replacement["length"]) is not int
                or replacement["length"] < 1
                or not isinstance(replacement["secret_sha256"], str)
                or not HEX64.fullmatch(replacement["secret_sha256"])
                or replacement["placeholder"] != "[REDACTED:NOMINAL]"
                or replacement["offset"] < prior_end
            ):
                raise ProtocolError("projection audit replacement is invalid or overlaps")
            prior_end = replacement["offset"] + replacement["length"]
        run_ids.append(record["run_id"])
        mode_labels.append((record["mode"], record["label"]))
    expected_runs = [f"r{index:03d}" for index in range(1, 121)]
    expected_mode_labels = {(mode, label) for mode in MODES for label in LABELS}
    if run_ids != expected_runs or set(mode_labels) != expected_mode_labels:
        raise ProtocolError(
            "projection audit manifest must exactly cover every run and mode/label"
        )
    return manifest


def validate_control_results(
    value: Any,
    control_manifest: dict[str, Any],
    expected_control_status: str = "DRAFT",
    atom_root: Path | None = None,
) -> dict[str, Any]:
    controls = validate_control_manifest(
        control_manifest, expected_control_status, atom_root
    )
    results = require_exact_keys(
        value, {"schema_version", "status", "records"}, "control results"
    )
    if (
        results["schema_version"] != 1
        or results["status"] != "DERIVED"
        or not isinstance(results["records"], list)
    ):
        raise ProtocolError("control-results identity/status mismatch")
    expected = controls["controls"]
    if len(results["records"]) != len(expected):
        raise ProtocolError("control results do not cover the control manifest")
    for raw_result, control in zip(results["records"], expected):
        result = require_exact_keys(
            raw_result,
            {"id", "family", "mode", "passed", "candidate_run_ids"},
            "control result",
        )
        if (
            result["id"] != control["id"]
            or result["family"] != control["family"]
            or result["mode"] != control["mode"]
            or type(result["passed"]) is not bool
            or not isinstance(result["candidate_run_ids"], list)
            or len(result["candidate_run_ids"]) != 5
            or len(set(result["candidate_run_ids"])) != 5
            or any(
                not isinstance(run_id, str) or REPORT_RUN_ID.fullmatch(run_id) is None
                for run_id in result["candidate_run_ids"]
            )
        ):
            raise ProtocolError("control result does not bind its manifest control")
    return results


def aggregate_context_core(document: dict[str, Any]) -> dict[str, Any]:
    return {
        key: document[key]
        for key in (
            "schema_version",
            "status",
            "builder_id",
            "static_lock_sha256",
            "rules_sha256",
            "input_digests",
            "context",
        )
    }


def validate_aggregate_context_document(value: Any) -> dict[str, Any]:
    document = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "builder_id",
            "static_lock_sha256",
            "rules_sha256",
            "input_digests",
            "context",
            "binding_sha256",
        },
        "aggregate context",
    )
    if (
        document["schema_version"] != 1
        or document["status"] != "DERIVED"
        or document["builder_id"] != AGGREGATE_BUILDER_ID
    ):
        raise ProtocolError("aggregate-context identity/status mismatch")
    for field in ("static_lock_sha256", "rules_sha256", "binding_sha256"):
        if not isinstance(document[field], str) or not HEX64.fullmatch(document[field]):
            raise ProtocolError(f"aggregate-context digest is invalid: {field}")
    digests = require_exact_keys(
        document["input_digests"], set(AGGREGATE_DIGEST_KEYS), "aggregate input digests"
    )
    if any(not isinstance(item, str) or not HEX64.fullmatch(item) for item in digests.values()):
        raise ProtocolError("aggregate context contains an invalid input digest")
    context = require_exact_keys(
        document["context"],
        {"oracle", "collection", "scores", "comparison", "review"},
        "aggregate gate context",
    )
    oracle = require_exact_keys(context["oracle"], {"coverage_pass"}, "oracle context")
    collection = require_exact_keys(
        context["collection"], {"complete", "invalid_output_count"}, "collection context"
    )
    scores = require_exact_keys(
        context["scores"],
        {
            "focused_recall_pass",
            "proof_quality_pass",
            "controls_pass",
            "hard_error_count",
            "global_defect_count",
            "material_finding_count",
        },
        "score context",
    )
    comparison = require_exact_keys(
        context["comparison"], {"predicate_pass"}, "comparison context"
    )
    review = require_exact_keys(context["review"], {"coherence_pass"}, "review context")
    booleans = [
        oracle["coverage_pass"],
        collection["complete"],
        scores["focused_recall_pass"],
        scores["proof_quality_pass"],
        scores["controls_pass"],
        comparison["predicate_pass"],
        review["coherence_pass"],
    ]
    integers = [
        collection["invalid_output_count"],
        scores["hard_error_count"],
        scores["global_defect_count"],
        scores["material_finding_count"],
    ]
    if any(type(item) is not bool for item in booleans) or any(
        type(item) is not int or item < 0 for item in integers
    ):
        raise ProtocolError("aggregate gate context contains an invalid typed value")
    if document["binding_sha256"] != sha256(
        canonical_json_bytes(aggregate_context_core(document))
    ):
        raise ProtocolError("aggregate-context binding digest mismatch")
    return document


def validate_aggregation_rules(
    value: Any,
    gate_manifest: dict[str, Any],
    expected_status: str = "DRAFT",
) -> dict[str, Any]:
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
        or rules["status"] != expected_status
        or rules["rules_version"] != "v5-diagnostic-aggregate-v1"
        or rules["default_dispositions"]
        != {"missing": "ERROR", "malformed": "ERROR", "error": "ERROR"}
    ):
        raise ProtocolError("aggregation rule identity/dispositions mismatch")
    expected_digest_keys = list(AGGREGATE_DIGEST_KEYS)
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


def expected_comparison_predicate(status: str = "DRAFT") -> dict[str, Any]:
    if status not in ("DRAFT", "READY"):
        raise ProtocolError("comparison predicate expected status is invalid")
    return {
        "schema_version": 1,
        "status": status,
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


def validate_comparison_predicate(
    value: Any, expected_status: str = "DRAFT"
) -> dict[str, Any]:
    if value != expected_comparison_predicate(expected_status):
        raise ProtocolError(
            f"comparison predicate does not exactly match the frozen {expected_status} formula"
        )
    return value


def validate_root_inventory(
    value: Any, expected_status: str = "DRAFT"
) -> dict[str, Any]:
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
        or inventory["status"] != expected_status
        or inventory["inventory_kind"] != "DIAGNOSTIC"
        or inventory["inventory_version"]
        != "v5-diagnostic-prequalification-draft-1"
        or inventory["scope"]
        != "Diagnostic rehearsal only; no admission, release, terminal look, or VN claim."
    ):
        raise ProtocolError(
            f"root inventory must be schema-v1 {expected_status} DIAGNOSTIC"
        )
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
    if roots != list(REQUIRED_ROOT_ORDER):
        raise ProtocolError("root inventory IDs are not the exact ordered V5 diagnostic roots")
    requirements = inventory["requirements"]
    if not isinstance(requirements, list) or len(requirements) != len(roots):
        raise ProtocolError("root inventory requirements are incomplete")
    requirement_ids: list[str] = []
    for index, raw in enumerate(requirements):
        requirement = require_exact_keys(raw, {"gate_id", "source", "summary"}, f"gate requirement {index}")
        if any(not isinstance(requirement[field], str) or not requirement[field].strip() for field in ("gate_id", "source", "summary")):
            raise ProtocolError(f"invalid root requirement {index}")
        requirement_ids.append(requirement["gate_id"])
        if requirement["source"] != ROOT_REQUIREMENT_SOURCES.get(
            requirement["gate_id"]
        ):
            raise ProtocolError(f"root requirement source drifted: {requirement['gate_id']}")
    if requirement_ids != list(REQUIRED_ROOT_ORDER):
        raise ProtocolError("root requirement mapping is not the exact ordered root inventory")
    return inventory


def validate_gate_manifest(
    value: Any, inventory: dict[str, Any], expected_status: str = "DRAFT"
) -> dict[str, Any]:
    inventory = validate_root_inventory(inventory, expected_status)
    manifest = require_exact_keys(
        value, {"schema_version", "status", "manifest_version", "gates"}, "gate manifest"
    )
    if (
        manifest["schema_version"] != 1
        or manifest["status"] != expected_status
        or manifest["manifest_version"]
        != "v5-diagnostic-prequalification-draft-1"
    ):
        raise ProtocolError(f"gate manifest must be schema-v1 {expected_status}")
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
        elif kind == "verified_bound_context":
            require_exact_keys(
                predicate, {"kind"}, f"gate {gate_id} predicate"
            )
            if inputs or gate_id != "D-STATIC-INTEGRITY":
                raise ProtocolError(
                    "verified-bound-context predicate is reserved for D-STATIC-INTEGRITY"
                )
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
    if ids != list(REQUIRED_ROOT_ORDER) or ids != roots:
        raise ProtocolError("gate IDs are not the exact ordered root inventory")
    for gate in gates:
        mechanics = {
            "prerequisites": gate["prerequisites"],
            "inputs": gate["inputs"],
            "predicate": gate["predicate"],
        }
        if mechanics != EXPECTED_GATE_MECHANICS[gate["id"]]:
            raise ProtocolError(f"frozen gate mechanics drifted: {gate['id']}")
    prerequisites = {gate["id"]: gate["prerequisites"] for gate in gates}
    topological_order(ids, prerequisites, "gate")
    expected_completion = {gate_id for gate_id in ids if gate_id.startswith("D-")} - {
        "D-DIAGNOSTIC-COMPLETION"
    }
    if set(prerequisites["D-DIAGNOSTIC-COMPLETION"]) != expected_completion:
        raise ProtocolError(
            "D-DIAGNOSTIC-COMPLETION must depend on every other D-* gate exactly once"
        )
    predicates = {gate["id"]: gate["predicate"] for gate in gates}
    for gate_id in ("G-ISOLATION", "G-OUTPUT-FINALIZATION"):
        if predicates[gate_id] != {"kind": "constant", "outcome": "FAIL"}:
            raise ProtocolError(f"{gate_id} must remain a direct constant FAIL")
    if predicates["D-STATIC-INTEGRITY"] != {"kind": "verified_bound_context"}:
        raise ProtocolError(
            "D-STATIC-INTEGRITY must be decided only by verified bound context"
        )
    return manifest


def context_lookup(context: dict[str, Any], path: str) -> Any:
    value: Any = context
    for part in path.split("."):
        if not isinstance(value, dict) or part not in value:
            raise KeyError(path)
        value = value[part]
    return value


def _evaluate_gate_context(
    manifest: dict[str, Any],
    inventory: dict[str, Any],
    context: dict[str, Any],
    *,
    verified_bound_context: bool,
    status: str,
    context_trust: str,
    static_lock_sha256: str | None,
    aggregate_context_sha256: str | None,
    contract_status: str,
) -> dict[str, Any]:
    if verified_bound_context:
        if (
            status != "LOCKED-COMPUTED"
            or context_trust != "STATIC_LOCK_AND_DERIVED_AGGREGATE_BOUND"
            or contract_status != "READY"
            or not isinstance(static_lock_sha256, str)
            or not HEX64.fullmatch(static_lock_sha256)
            or not isinstance(aggregate_context_sha256, str)
            or not HEX64.fullmatch(aggregate_context_sha256)
        ):
            raise ProtocolError("bound gate evaluation identity/bindings are invalid")
    elif (
        status != "DRAFT-COMPUTED"
        or context_trust != "UNBOUND_DRAFT_INPUT"
        or contract_status != "DRAFT"
        or static_lock_sha256 is not None
        or aggregate_context_sha256 is not None
    ):
        raise ProtocolError("unbound gate evaluation identity/bindings are invalid")
    manifest = validate_gate_manifest(manifest, inventory, contract_status)
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
        elif predicate["kind"] == "verified_bound_context":
            direct = "PASS" if verified_bound_context else "FAIL"
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
        "status": status,
        "manifest_version": manifest["manifest_version"],
        "context_trust": context_trust,
        "static_lock_sha256": static_lock_sha256,
        "aggregate_context_sha256": aggregate_context_sha256,
        "release_eligibility": copy.deepcopy(inventory["release_eligibility"]),
        "gates": [results[gate["id"]] for gate in gates],
    }


def evaluate_gates(
    manifest: dict[str, Any], inventory: dict[str, Any], context: dict[str, Any]
) -> dict[str, Any]:
    """Evaluate caller-provided context only as explicitly unbound DRAFT input."""

    return _evaluate_gate_context(
        manifest,
        inventory,
        context,
        verified_bound_context=False,
        status="DRAFT-COMPUTED",
        context_trust="UNBOUND_DRAFT_INPUT",
        static_lock_sha256=None,
        aggregate_context_sha256=None,
        contract_status="DRAFT",
    )


def validate_bound_aggregate_receipts(
    static_root: Path, aggregate: dict[str, Any]
) -> dict[str, str]:
    aggregation_root = static_root / "runtime" / "state" / "aggregation"
    receipt_root = aggregation_root / "integration-receipts"
    if (
        not receipt_root.is_dir()
        or receipt_root.is_symlink()
        or receipt_root.lstat().st_mode & 0o222
    ):
        raise ProtocolError("bound aggregate receipt directory must be immutable")
    expected_names = {f"{hook_id}.json" for hook_id in POSTLOCK_RECEIPT_HOOK_IDS}
    actual_names = {path.name for path in receipt_root.iterdir()}
    if actual_names != expected_names:
        raise ProtocolError("bound aggregate receipt file set is not exact")
    receipt_digests: dict[str, str] = {}
    receipts: dict[str, dict[str, Any]] = {}
    for hook_id in POSTLOCK_RECEIPT_HOOK_IDS:
        path = receipt_root / f"{hook_id}.json"
        receipt = validate_integration_receipt(
            read_committed_json(path, f"post-lock receipt {hook_id}"),
            hook_id,
            INTEGRATION_HOOK_PHASES[hook_id],
        )
        if path.read_bytes() != canonical_json_bytes(receipt):
            raise ProtocolError(f"post-lock receipt is not canonical JSON: {hook_id}")
        receipts[hook_id] = receipt
        receipt_digests[hook_id] = sha256(path.read_bytes())
    aggregate_path = aggregation_root / "aggregate-context.json"
    aggregate_bytes = aggregate_path.read_bytes()
    if aggregate_bytes != canonical_json_bytes(aggregate):
        raise ProtocolError("stored aggregate context is not canonical JSON")
    aggregate_sha = sha256(aggregate_bytes)
    common_inputs = {
        **aggregate["input_digests"],
        "static_lock_sha256": aggregate["static_lock_sha256"],
        "rules_sha256": aggregate["rules_sha256"],
    }
    runtime_outputs = {
        "H-ENFORCE-WORD-COUNTER": {
            "validated_word_counts_sha256": aggregate["input_digests"][
                "word_counts_sha256"
            ]
        },
        "H-BUILD-VALIDATE-SCORER-REPORT-PROJECTIONS": {
            "validated_projection_audit_manifest_sha256": aggregate[
                "input_digests"
            ]["projection_audit_manifest_sha256"]
        },
        "H-VALIDATE-SCHEDULE-LEASE-ATTEMPT-LEDGER": {
            "validated_schedule_slots_sha256": aggregate["input_digests"][
                "schedule_slots_sha256"
            ],
            "validated_envelopes_sha256": aggregate["input_digests"][
                "envelopes_sha256"
            ],
        },
        "H-SEMANTICALLY-REVALIDATE-ENVELOPES": {
            "validated_envelopes_sha256": aggregate["input_digests"][
                "envelopes_sha256"
            ]
        },
        "H-VALIDATE-EVALUATOR-INDEPENDENCE-QUALIFICATION": {
            "validated_scoring_bundle_manifest_sha256": aggregate[
                "input_digests"
            ]["scoring_bundle_manifest_sha256"]
        },
        "H-RUN-VALIDATE-MATERIALITY-REVIEWS": {
            "validated_materiality_ledger_sha256": aggregate["input_digests"][
                "materiality_ledger_sha256"
            ]
        },
    }
    for hook_id, outputs in runtime_outputs.items():
        receipt = receipts[hook_id]
        if receipt["input_digests"] != common_inputs or receipt["output_digests"] != outputs:
            raise ProtocolError(f"runtime receipt does not bind its exact artifact set: {hook_id}")
    derive = receipts["H-DERIVE-AGGREGATE-CONTEXT"]
    expected_derive_inputs = common_inputs
    if (
        derive["input_digests"] != expected_derive_inputs
        or derive["output_digests"] != {"aggregate_context_sha256": aggregate_sha}
    ):
        raise ProtocolError("aggregate derivation receipt does not bind exact inputs/output")
    bind = receipts["H-BIND-CONTEXT-INPUT-DIGESTS"]
    bind_inputs = {
        "static_lock_sha256": aggregate["static_lock_sha256"],
        "rules_sha256": aggregate["rules_sha256"],
        "aggregate_context_sha256": aggregate_sha,
        **{
            f"receipt::{hook_id}": receipt_digests[hook_id]
            for hook_id in PRE_BIND_RECEIPT_HOOK_IDS
        },
    }
    expected_binding = sha256(canonical_json_bytes(bind_inputs))
    if (
        bind["input_digests"] != bind_inputs
        or bind["output_digests"] != {"bound_gate_context_sha256": expected_binding}
    ):
        raise ProtocolError("context-binding receipt is not the exact terminal binding")
    return receipt_digests


def evaluate_bound_gates(
    static_root: Path, external_commitment_path: Path | None = None
) -> dict[str, Any]:
    root, _lock, _reviewer_ids = load_verified_static_bundle(
        static_root, external_commitment_path
    )
    aggregate_path = root / "runtime" / "state" / "aggregation" / "aggregate-context.json"
    aggregate = validate_aggregate_context_document(
        read_committed_json(aggregate_path, "stored aggregate context")
    )
    rederived = derive_aggregate_context(root, external_commitment_path)
    if aggregate != rederived:
        raise ProtocolError("stored aggregate context is not the deterministic derivation")
    lock_sha = sha256((root / "STATIC-LOCK.json").read_bytes())
    rules_sha = sha256((root / "aggregation-rules.json").read_bytes())
    if (
        aggregate["static_lock_sha256"] != lock_sha
        or aggregate["rules_sha256"] != rules_sha
    ):
        raise ProtocolError("aggregate context does not bind the verified static inputs")
    validate_bound_aggregate_receipts(root, aggregate)
    return _evaluate_gate_context(
        read_json(root / "gate-manifest.json"),
        read_json(root / "root-inventory.json"),
        aggregate["context"],
        verified_bound_context=True,
        status="LOCKED-COMPUTED",
        context_trust="STATIC_LOCK_AND_DERIVED_AGGREGATE_BOUND",
        static_lock_sha256=lock_sha,
        aggregate_context_sha256=sha256(canonical_json_bytes(aggregate)),
        contract_status="READY",
    )


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
    if role not in SEMANTIC_AGENT_ROLES:
        raise ProtocolError("invalid launch semantic-agent role")
    require_safe_id(record["assignment_id"], "launch assignment ID")
    require_safe_id(record["slot_id"], "launch slot ID")
    if not isinstance(record["cell_id"], str) or not re.fullmatch(r"[0-9a-f]{32}", record["cell_id"]):
        raise ProtocolError("launch cell_id must be 128-bit lowercase hex")
    mode = record["mode"]
    if role in GLOBAL_EVALUATOR_ROLES:
        if mode is not None:
            raise ProtocolError("global materiality launch mode must be null")
    elif mode not in MODES:
        raise ProtocolError("launch mode is invalid")
    if role == "report":
        if not isinstance(record["run_id"], str) or REPORT_RUN_ID.fullmatch(
            record["run_id"]
        ) is None:
            raise ProtocolError("report launch run_id must be exactly r001 through r120")
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
        workspace = Path(workspace_root)
        if (
            record["input_root"] != str(workspace / "input")
            or record["output_root"] != str(workspace / "output")
        ):
            raise ProtocolError(
                "report launch input/output roots must be exact workspace children"
            )
        target_path = require_relative_file(record["target_path"], "launch target path")
        authority_path = require_relative_file(
            record["authority_packet_path"], "launch authority packet path"
        )
        require_relative_file(record["output_path"], "launch output path")
        input_workspace = Path(record["input_root"])
        for relative, label in ((target_path, "target"), (authority_path, "authority")):
            resolved = (input_workspace / Path(*PurePosixPath(relative).parts)).resolve()
            if not is_within(resolved, input_workspace):
                raise ProtocolError(f"launch {label} path escapes the exact input root")
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
            "materiality-reviewer": r"m[12]",
            "materiality-adjudicator": r"ma1",
        }[role]
        if re.fullmatch(expected_assignment, assignment) is None:
            raise ProtocolError("evaluator launch role/assignment mismatch")
        workspace_root = require_normalized_absolute_path_string(
            record["workspace_root"], "evaluator workspace_root"
        )
        workspace = Path(workspace_root)
        if (
            record["input_root"] != str(workspace / "input")
            or record["output_root"] != str(workspace / "output")
        ):
            raise ProtocolError(
                "evaluator launch input/output roots must be exact workspace children"
            )
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
    if not isinstance(record["schema_paths"], list):
        raise ProtocolError("launch schema paths must be a list")
    schema_paths = [
        require_relative_file(path, "launch schema path") for path in record["schema_paths"]
    ]
    if schema_paths != sorted(schema_paths) or len(schema_paths) != len(set(schema_paths)):
        raise ProtocolError("launch schema paths must be unique and sorted")
    if role == "report" and schema_paths:
        raise ProtocolError("report launches must expose no evaluator output schemas")
    if role != "report" and not schema_paths:
        raise ProtocolError("evaluator launches must bind their exact output schema")
    for schema_path in schema_paths:
        if not schema_path.startswith("schemas/") or not schema_path.endswith(
            ".schema.json"
        ):
            raise ProtocolError("launch schema path is not in the schemas namespace")
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


def evaluator_contract_index(documents: dict[str, Any]) -> dict[str, dict[str, Any]]:
    contract = documents.get("evaluator-launch-contracts")
    if (
        not isinstance(contract, dict)
        or contract.get("schema_version") != 1
        or contract.get("status") != "READY"
        or contract.get("contract_id") != "v5-evaluator-runtime-instantiation-v1"
        or contract.get("input_alias") != "input"
        or contract.get("output_alias") != "output"
        or contract.get("input_packet_path") != "packet.json"
        or not isinstance(contract.get("assignments"), list)
    ):
        raise ProtocolError("evaluator launch contract identity/status is invalid")
    index: dict[str, dict[str, Any]] = {}
    for row in contract["assignments"]:
        if not isinstance(row, dict) or not isinstance(row.get("assignment_id"), str):
            raise ProtocolError("evaluator launch contract assignment is invalid")
        assignment = row["assignment_id"]
        if assignment in index:
            raise ProtocolError("evaluator launch contract has duplicate assignments")
        index[assignment] = row
    if len(index) != 43:
        raise ProtocolError("evaluator launch contract must contain exactly 43 assignments")
    return index


def evaluator_workspace_base(documents: dict[str, Any]) -> Path:
    launches = documents.get("report-launch-records")
    if not isinstance(launches, list) or len(launches) != 120:
        raise ProtocolError("evaluator workspace derivation lacks the report launch inventory")
    bases = {Path(launch["workspace_root"]).parent for launch in launches}
    if len(bases) != 1:
        raise ProtocolError("report launches do not bind one evaluator workspace base")
    return next(iter(bases))


def validate_evaluator_packet_for_role(
    packet: Any, row: dict[str, Any]
) -> dict[str, Any]:
    role = row["role"]
    if role == "scorer":
        return validate_score_input_packet(packet, row["mode"], row["reviewer_id"])
    if role == "consistency":
        return validate_consistency_packet(packet)
    if role == "adjudicator":
        return validate_adjudication_packet(packet)
    if role == "materiality-reviewer":
        return validate_materiality_review_packet(packet, "READY")
    if role == "materiality-adjudicator":
        return validate_materiality_adjudication_packet(packet, "READY")
    raise ProtocolError("unknown evaluator launch-contract role")


def build_expected_evaluator_launch(
    static_root: Path,
    documents: dict[str, Any],
    assignment_id: str,
    packet_bytes: bytes,
) -> tuple[dict[str, Any], dict[str, Any]]:
    rows = evaluator_contract_index(documents)
    row = rows.get(assignment_id)
    if row is None:
        raise ProtocolError(f"unknown evaluator assignment: {assignment_id}")
    packet = strict_json_loads(packet_bytes, "evaluator input packet")
    if packet_bytes != canonical_json_bytes(packet):
        raise ProtocolError("evaluator input packet bytes are not canonical JSON")
    validate_evaluator_packet_for_role(packet, row)
    if row["launch_condition"] == "IF_INPUT_PACKET_NONEMPTY" and not packet.get("cells"):
        raise ProtocolError("conditional evaluator launch has an empty input packet")
    contract_bytes = (
        static_root
        / "static"
        / "generated"
        / "evaluator-launch-contracts.json"
    ).read_bytes()
    schedule_sha = sha256(contract_bytes)
    workspace_leaf = sha256(
        b"v5-evaluator-workspace-v1\0"
        + bytes.fromhex(schedule_sha)
        + b"\0"
        + assignment_id.encode("utf-8")
    )
    workspace = evaluator_workspace_base(documents) / workspace_leaf
    launch = {
        "schema_version": 1,
        "status": "READY",
        "role": row["role"],
        "assignment_id": assignment_id,
        "slot_id": assignment_id,
        "run_id": None,
        "cell_id": workspace_leaf[:32],
        "mode": row["mode"],
        "fixture_id": None,
        "task_mode": None,
        "prompt_regime": None,
        "condition_role": None,
        "condition_label": None,
        "target_label": None,
        "replicate": None,
        "workspace_root": str(workspace),
        "input_root": str(workspace / "input"),
        "output_root": str(workspace / "output"),
        "target_path": None,
        "output_path": row["output_path"],
        "schema_paths": row["schema_paths"],
        "schedule_sha256": schedule_sha,
        "prompt_sha256": row["prompt_sha256"],
        "package_byte_tree_sha256": None,
        "target_byte_tree_sha256": None,
        "authority_packet_path": None,
        "authority_packet_sha256": None,
        "authority_packet_visibility": None,
        "execution_manifest_sha256": row["execution_manifest_sha256"],
        "input_packet_sha256": sha256(packet_bytes),
        "envelope_spec_sha256": row["envelope_spec_sha256"],
    }
    return validate_launch_record(launch), row


def verify_evaluator_input_tree(
    input_root: Path,
    static_root: Path,
    row: dict[str, Any],
    packet_bytes: bytes,
) -> None:
    if input_root.is_symlink() or not input_root.is_dir():
        raise ProtocolError("evaluator input root is not a real directory")
    expected_files = {
        row["input_packet_path"]: packet_bytes,
        **{
            schema_path: (static_root / Path(*PurePosixPath(schema_path).parts)).read_bytes()
            for schema_path in row["schema_paths"]
        },
    }
    actual_files: set[str] = set()
    for path in input_root.rglob("*"):
        relative = path.relative_to(input_root).as_posix()
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ProtocolError(f"evaluator input tree has an unsupported entry: {relative}")
        if path.is_file():
            actual_files.add(relative)
            if relative not in expected_files or path.read_bytes() != expected_files[relative]:
                raise ProtocolError(f"evaluator input file substitution: {relative}")
    if actual_files != set(expected_files):
        raise ProtocolError("evaluator input file set is not exact")


def materialize_evaluator_input_tree(
    input_root: Path,
    static_root: Path,
    row: dict[str, Any],
    packet_bytes: bytes,
) -> None:
    if input_root.exists():
        verify_evaluator_input_tree(input_root, static_root, row, packet_bytes)
        harden_tree_read_only(input_root)
        return
    if not input_root.parent.is_dir() or input_root.parent.is_symlink():
        raise ProtocolError("evaluator workspace root must already be a real directory")
    stage = Path(tempfile.mkdtemp(prefix=".evaluator-input-stage-", dir=input_root.parent))
    try:
        files = {
            row["input_packet_path"]: packet_bytes,
            **{
                schema_path: (
                    static_root / Path(*PurePosixPath(schema_path).parts)
                ).read_bytes()
                for schema_path in row["schema_paths"]
            },
        }
        for relative, data in files.items():
            destination = stage / Path(*PurePosixPath(relative).parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            exclusive_write(destination, data)
        verify_evaluator_input_tree(stage, static_root, row, packet_bytes)
        harden_tree_read_only(stage)
        try:
            os.rename(stage, input_root)
        except FileExistsError:
            verify_evaluator_input_tree(input_root, static_root, row, packet_bytes)
            harden_tree_read_only(input_root)
        fsync_directory(input_root.parent)
    finally:
        if stage.exists():
            os.chmod(stage, 0o700)
            shutil.rmtree(stage)


def validate_report_input_plan(
    value: Any, launch: dict[str, Any]
) -> dict[str, Any]:
    launch = validate_launch_record(launch)
    if launch["role"] != "report":
        raise ProtocolError("report input plan requires a report launch")
    plan = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "run_id",
            "cell_id",
            "input_alias",
            "output_alias",
            "entries",
        },
        "report input plan",
    )
    if (
        plan["schema_version"] != 1
        or plan["status"] != "READY"
        or plan["run_id"] != launch["run_id"]
        or plan["cell_id"] != launch["cell_id"]
        or plan["input_alias"] != "input"
        or plan["output_alias"] != "output"
        or not isinstance(plan["entries"], list)
    ):
        raise ProtocolError("report input plan identity/status mismatch")
    entries: dict[str, dict[str, Any]] = {}
    for raw in plan["entries"]:
        entry = require_exact_keys(
            raw,
            {"destination", "kind", "source_path", "sha256"},
            "report input plan entry",
        )
        destination = require_relative_file(
            entry["destination"], "report input destination"
        )
        source_path = require_relative_file(
            entry["source_path"], "report input source path"
        )
        if (
            not destination.startswith("input/")
            or destination in entries
            or entry["kind"] not in ("FILE", "BYTE_TREE_V1_DIRECTORY")
            or not isinstance(entry["sha256"], str)
            or not HEX64.fullmatch(entry["sha256"])
        ):
            raise ProtocolError("report input plan entry is invalid or duplicated")
        entries[destination] = {**entry, "source_path": source_path}
    expected: dict[str, tuple[str, str | None]] = {
        "input/target": (
            "BYTE_TREE_V1_DIRECTORY",
            launch["target_byte_tree_sha256"],
        ),
        "input/docs/rust-documentation.json": (
            "FILE",
            launch["authority_packet_sha256"],
        ),
        **{
            f"input/{schema_path}": ("FILE", None)
            for schema_path in launch["schema_paths"]
        },
    }
    if launch["condition_role"] == "no_skill":
        if launch["package_byte_tree_sha256"] is not None:
            raise ProtocolError("no-skill report launch unexpectedly binds a package")
    else:
        expected["input/package"] = (
            "BYTE_TREE_V1_DIRECTORY",
            launch["package_byte_tree_sha256"],
        )
    if set(entries) != set(expected):
        raise ProtocolError(
            "report input plan does not exactly cover target, authority, schemas, and package"
        )
    for destination, (kind, digest) in expected.items():
        entry = entries[destination]
        if entry["kind"] != kind or (digest is not None and entry["sha256"] != digest):
            raise ProtocolError(f"report input plan launch binding mismatch: {destination}")
        if destination.startswith("input/schemas/") and entry["source_path"] != destination[6:]:
            raise ProtocolError("report input schema source/destination mismatch")
    ordered = [entry["destination"] for entry in plan["entries"]]
    if ordered != sorted(ordered):
        raise ProtocolError("report input plan entries must be sorted by destination")
    return plan


def verify_report_input_tree(
    input_root: Path,
    static_root: Path,
    plan: dict[str, Any],
    byte_tree_v1: Callable[[Path], str],
) -> None:
    if input_root.is_symlink() or not input_root.is_dir():
        raise ProtocolError("report input root must be a real materialized directory")
    allowed_files: set[str] = set()
    allowed_directories: set[str] = set()
    directory_prefixes: list[str] = []
    for entry in plan["entries"]:
        relative = PurePosixPath(entry["destination"]).relative_to("input").as_posix()
        destination = input_root / Path(*PurePosixPath(relative).parts)
        source = static_root / Path(*PurePosixPath(entry["source_path"]).parts)
        if not is_within(source.resolve(), static_root):
            raise ProtocolError("report input source escapes the verified static root")
        for parent in PurePosixPath(relative).parents:
            if parent.as_posix() not in (".", ""):
                allowed_directories.add(parent.as_posix())
        if entry["kind"] == "FILE":
            if source.is_symlink() or not source.is_file():
                raise ProtocolError(f"report input source is not a regular file: {source}")
            source_bytes = source.read_bytes()
            if sha256(source_bytes) != entry["sha256"]:
                raise ProtocolError(f"report input source digest mismatch: {source}")
            if destination.is_symlink() or not destination.is_file():
                raise ProtocolError(f"report input file is missing: {relative}")
            if destination.read_bytes() != source_bytes:
                raise ProtocolError(f"report input file substitution: {relative}")
            allowed_files.add(relative)
        else:
            if source.is_symlink() or not source.is_dir():
                raise ProtocolError(f"report input source is not a real directory: {source}")
            try:
                source_digest = byte_tree_v1(source)
                destination_digest = byte_tree_v1(destination)
            except Exception as error:
                raise ProtocolError(f"report input directory is invalid: {relative}") from error
            if source_digest != entry["sha256"] or destination_digest != entry["sha256"]:
                raise ProtocolError(f"report input directory substitution: {relative}")
            directory_prefixes.append(relative + "/")
            allowed_directories.add(relative)
    for path in input_root.rglob("*"):
        relative = path.relative_to(input_root).as_posix()
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ProtocolError(f"report input tree has unsupported entry: {relative}")
        if path.is_dir():
            allowed = relative in allowed_directories or any(
                relative.startswith(prefix) for prefix in directory_prefixes
            )
        else:
            allowed = relative in allowed_files or any(
                relative.startswith(prefix) for prefix in directory_prefixes
            )
        if not allowed:
            raise ProtocolError(f"report input tree has an undeclared entry: {relative}")


def materialize_report_input_tree(
    input_root: Path,
    static_root: Path,
    plan: dict[str, Any],
    byte_tree_v1: Callable[[Path], str],
) -> None:
    if input_root.exists():
        verify_report_input_tree(input_root, static_root, plan, byte_tree_v1)
        harden_tree_read_only(input_root)
        return
    if not input_root.parent.is_dir() or input_root.parent.is_symlink():
        raise ProtocolError("report workspace root must already be a real directory")
    stage = Path(tempfile.mkdtemp(prefix=".input-stage-", dir=input_root.parent))
    try:
        for entry in plan["entries"]:
            relative = PurePosixPath(entry["destination"]).relative_to("input").as_posix()
            destination = stage / Path(*PurePosixPath(relative).parts)
            source = static_root / Path(*PurePosixPath(entry["source_path"]).parts)
            destination.parent.mkdir(parents=True, exist_ok=True)
            if entry["kind"] == "FILE":
                source_bytes = source.read_bytes()
                exclusive_write(destination, source_bytes)
            else:
                shutil.copytree(source, destination, symlinks=False)
        verify_report_input_tree(stage, static_root, plan, byte_tree_v1)
        harden_tree_read_only(stage)
        try:
            os.rename(stage, input_root)
        except FileExistsError:
            verify_report_input_tree(input_root, static_root, plan, byte_tree_v1)
            harden_tree_read_only(input_root)
        fsync_directory(input_root.parent)
    finally:
        if stage.exists():
            os.chmod(stage, 0o700)
            shutil.rmtree(stage)


def materialize_bound_report_inputs(
    launch_path: Path,
    input_packet_path: Path,
    launch: dict[str, Any],
    plan: dict[str, Any],
    verified_static_root: Path,
) -> None:
    input_packet_absolute = Path(os.path.abspath(os.fspath(input_packet_path)))
    try:
        static_root = input_packet_absolute.parents[3]
    except IndexError as error:
        raise ProtocolError("report input-plan path has no static bundle root") from error
    expected_plan = (
        static_root
        / "static"
        / "generated"
        / "report-input-plans"
        / f"{launch['run_id']}.json"
    )
    expected_launch = (
        static_root
        / "static"
        / "generated"
        / "launch-records"
        / f"{launch['run_id']}.json"
    )
    if input_packet_absolute != expected_plan or Path(
        os.path.abspath(os.fspath(launch_path))
    ) != expected_launch:
        raise ProtocolError(
            "report lease paths must be the locked generated launch and input plan"
        )
    if static_root != verified_static_root:
        raise ProtocolError("report input-plan root is not the verified static root")
    preparation = run_trusted_module("prepare.py", "v5_report_input_byte_tree")
    input_root = Path(launch["input_root"])
    materialize_report_input_tree(
        input_root, verified_static_root, plan, preparation["byte_tree_v1"]
    )
    verify_report_input_tree(
        input_root, verified_static_root, plan, preparation["byte_tree_v1"]
    )


def validate_schedule_launch_ids(
    schedule: Any, launches: list[dict[str, Any]]
) -> dict[str, Any]:
    schedule = require_exact_keys(
        schedule, {"schema_version", "status", "slots"}, "launch schedule"
    )
    if (
        schedule["schema_version"] != 1
        or schedule["status"] not in ("DRAFT-GENERATED-UNVERIFIED", "READY")
        or not isinstance(schedule["slots"], list)
        or len(schedule["slots"]) != 120
        or not isinstance(launches, list)
        or len(launches) != 120
    ):
        raise ProtocolError("schedule/launch inventory must contain exactly 120 records")
    schedule_by_run: dict[str, dict[str, Any]] = {}
    for raw in schedule["slots"]:
        if not isinstance(raw, dict):
            raise ProtocolError("launch schedule slot must be an object")
        run_id = raw.get("run_id")
        cell_id = raw.get("cell_id")
        if (
            not isinstance(run_id, str)
            or REPORT_RUN_ID.fullmatch(run_id) is None
            or run_id in schedule_by_run
            or not isinstance(cell_id, str)
            or re.fullmatch(r"[0-9a-f]{32}", cell_id) is None
        ):
            raise ProtocolError("launch schedule run/cell identity is invalid")
        schedule_by_run[run_id] = raw
    expected_ids = {f"r{index:03d}" for index in range(1, 121)}
    if set(schedule_by_run) != expected_ids:
        raise ProtocolError("launch schedule IDs must be exactly r001 through r120")
    launch_by_run: dict[str, dict[str, Any]] = {}
    for raw in launches:
        launch = validate_launch_record(raw)
        if launch["role"] != "report" or launch["run_id"] in launch_by_run:
            raise ProtocolError("schedule launch inventory must contain unique report launches")
        launch_by_run[launch["run_id"]] = launch
    if set(launch_by_run) != expected_ids:
        raise ProtocolError("launch record IDs must be exactly r001 through r120")
    for run_id in sorted(expected_ids):
        slot = schedule_by_run[run_id]
        launch = launch_by_run[run_id]
        if (
            launch["slot_id"] != run_id
            or launch["assignment_id"] != run_id
            or launch["cell_id"] != slot["cell_id"]
            or launch["replicate"] != slot.get("replicate")
            or launch["condition_label"] != slot.get("condition_label")
            or launch["target_label"] != slot.get("target_label")
            or launch["prompt_regime"] != slot.get("prompt_regime")
        ):
            raise ProtocolError(f"schedule/launch identity mismatch: {run_id}")
    return {"schema_version": 1, "status": "SCHEDULE-LAUNCH-IDS-VALID", "run_ids": sorted(expected_ids)}


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
    value = strict_json_loads(data, "lease envelope spec")
    return validate_envelope_spec(value, require_ready=True)


def load_bound_launch(lease: dict[str, Any]) -> dict[str, Any]:
    try:
        data = base64.b64decode(lease["launch_record_bytes_base64"], validate=True)
    except Exception as error:
        raise ProtocolError("lease launch-record encoding is invalid") from error
    if sha256(data) != lease.get("launch_record_sha256"):
        raise ProtocolError("lease launch-record digest mismatch")
    value = strict_json_loads(data, "lease launch record")
    launch = validate_launch_record(value)
    if launch["slot_id"] != lease.get("slot_id"):
        raise ProtocolError("lease/launch slot mismatch")
    return launch


def load_bound_input_packet(lease: dict[str, Any]) -> Any:
    return strict_json_loads(load_bound_input_packet_bytes(lease), "lease input packet")


def load_bound_input_packet_bytes(lease: dict[str, Any]) -> bytes:
    try:
        data = base64.b64decode(lease["input_packet_bytes_base64"], validate=True)
    except Exception as error:
        raise ProtocolError("lease input-packet encoding is invalid") from error
    if sha256(data) != lease.get("input_packet_sha256"):
        raise ProtocolError("lease input-packet digest mismatch")
    return data


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
            "input_packet_sha256",
            "input_packet_bytes_base64",
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
        "input_packet_sha256",
    ):
        if not isinstance(lease[field], str) or not HEX64.fullmatch(lease[field]):
            raise ProtocolError(f"invalid lease digest: {field}")
    bound_root = require_normalized_absolute_path_string(
        lease["attempt_root"], "lease attempt_root"
    )
    if sha256(bound_root.encode("utf-8")) != lease["attempt_root_claim_sha256"]:
        raise ProtocolError("lease attempt-root claim digest mismatch")
    launch = load_bound_launch(lease)
    load_bound_spec(lease)
    load_bound_input_packet(lease)
    if (
        launch["output_root"] != bound_root
        or launch["envelope_spec_sha256"] != lease["envelope_spec_sha256"]
        or launch["input_packet_sha256"] != lease["input_packet_sha256"]
    ):
        raise ProtocolError("lease launch/output/spec/input cross-binding mismatch")
    return lease


def _write_or_validate_immutable(path: Path, value: dict[str, Any]) -> None:
    expected = canonical_json_bytes(value)
    if path.exists():
        if (
            not path.is_file()
            or path.is_symlink()
            or path.read_bytes() != expected
            or path.lstat().st_mode & 0o222
        ):
            raise ProtocolError(f"immutable ledger mismatch: {path}")
        return
    exclusive_write(path, expected)
    os.chmod(path, 0o400)
    fsync_directory(path.parent)


def _authoritative_leases(
    state_root: Path,
    *,
    production_reviewer_ids: frozenset[str] | None = None,
) -> list[dict[str, Any]]:
    slots_root = state_root / "slots"
    if not slots_root.exists():
        return []
    if not slots_root.is_dir() or slots_root.is_symlink():
        raise ProtocolError("protocol slots root is not a regular directory")
    leases: list[dict[str, Any]] = []
    for slot_path in sorted(slots_root.iterdir(), key=lambda item: item.name):
        if not slot_path.is_dir() or slot_path.is_symlink():
            raise ProtocolError("protocol slots root contains a non-directory entry")
        require_safe_id(slot_path.name, "slot directory")
        lease_path = slot_path / "lease.json"
        if not lease_path.is_file() or lease_path.is_symlink():
            raise ProtocolError(f"slot {slot_path.name} lacks its authoritative lease")
        lease = validate_lease(read_json(lease_path))
        if lease["slot_id"] != slot_path.name:
            raise ProtocolError("authoritative lease/slot directory mismatch")
        if production_reviewer_ids is not None:
            require_production_runtime_actor(
                lease["agent_id"],
                "persisted production lease agent ID",
                production_reviewer_ids,
            )
        leases.append(lease)
    return leases


def acquire_lease(
    state_root: Path,
    launch_path: Path,
    agent_id: str,
    spec_path: Path,
    attempt_root: Path,
    input_packet_path: Path,
    *,
    fault_after: str | None = None,
    static_root: Path | None = None,
    external_commitment_path: Path | None = None,
    test_capability: object | None = None,
) -> dict[str, Any]:
    state_root, verified_root, production_reviewer_ids = require_state_context(
        state_root,
        static_root=static_root,
        external_commitment_path=external_commitment_path,
        test_capability=test_capability,
    )
    agent_id = require_safe_id(agent_id, "agent ID")
    if static_root is not None:
        require_production_actor_id(agent_id, "production agent ID")
    launch_bytes = launch_path.read_bytes()
    launch = validate_launch_record(strict_json_loads(launch_bytes, "launch record"))
    slot_id = launch["slot_id"]
    spec_bytes = spec_path.read_bytes()
    spec = strict_json_loads(spec_bytes, "envelope spec")
    validate_envelope_spec(spec, require_ready=True)
    if sha256(spec_bytes) != launch["envelope_spec_sha256"]:
        raise ProtocolError("launch record/envelope-spec digest mismatch")
    if launch["output_path"] not in {
        item["path"] for item in spec["files"]
    }:
        raise ProtocolError("launch output path is not declared by its envelope spec")
    input_packet_bytes = input_packet_path.read_bytes()
    input_packet = strict_json_loads(input_packet_bytes, "launch input packet")
    if sha256(input_packet_bytes) != launch["input_packet_sha256"]:
        raise ProtocolError("launch record/input-packet digest mismatch")
    evaluator_row: dict[str, Any] | None = None
    if static_root is not None:
        if verified_root is None or production_reviewer_ids is None:
            raise ProtocolError("production state context is incomplete")
        require_production_runtime_actor(
            agent_id, "production agent ID", production_reviewer_ids
        )
        # Reject a pre-existing poisoned peer before materializing any launch
        # input. The authoritative set is checked again under the mutation lock
        # below, so a cooperating concurrent writer cannot race this preflight.
        with operation_lock(state_root):
            _authoritative_leases(
                state_root, production_reviewer_ids=production_reviewer_ids
            )
    if launch["role"] != "report" and verified_root is not None:
        documents = load_ready_generated_documents(verified_root)
        expected_launch, evaluator_row = build_expected_evaluator_launch(
            verified_root, documents, launch["assignment_id"], input_packet_bytes
        )
        if launch != expected_launch or launch_bytes != canonical_json_bytes(expected_launch):
            raise ProtocolError("evaluator launch is not the exact deterministic instantiation")
        expected_spec_path = verified_root / Path(
            *PurePosixPath(evaluator_row["envelope_spec_path"]).parts
        )
        if Path(os.path.abspath(os.fspath(spec_path))) != expected_spec_path:
            raise ProtocolError("evaluator lease did not use the locked role envelope spec")
        materialize_evaluator_input_tree(
            Path(launch["input_root"]),
            verified_root,
            evaluator_row,
            input_packet_bytes,
        )
    elif launch["role"] == "report" and verified_root is not None:
        # Do not treat the locked launch's target/package digests as
        # self-authenticating.  Rebuild all report material from the
        # authenticated condition map, target map, package/target identities,
        # schedule, reviewed values, and role contracts before materializing
        # any agent-visible byte.
        ready_documents = load_ready_generated_documents(verified_root)
        expected_launch_path = (
            verified_root
            / "static"
            / "generated"
            / "launch-records"
            / f"{launch['run_id']}.json"
        )
        expected_plan_path = (
            verified_root
            / "static"
            / "generated"
            / "report-input-plans"
            / f"{launch['run_id']}.json"
        )
        if (
            Path(os.path.abspath(os.fspath(launch_path))) != expected_launch_path
            or Path(os.path.abspath(os.fspath(input_packet_path))) != expected_plan_path
            or launch_bytes != expected_launch_path.read_bytes()
            or input_packet_bytes != expected_plan_path.read_bytes()
        ):
            raise ProtocolError("report lease artifacts are not from the bound static root")
        expected_launch = next(
            item
            for item in ready_documents["report-launch-records"]
            if item["run_id"] == launch["run_id"]
        )
        if launch != expected_launch:
            raise ProtocolError("report lease launch is not the authenticated map derivation")
    report_plan = (
        validate_report_input_plan(input_packet, launch)
        if launch["role"] == "report"
        else None
    )
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
    if report_plan is not None:
        if verified_root is None:
            raise ProtocolError("report input materialization lacks a verified static root")
        materialize_bound_report_inputs(
            launch_path,
            input_packet_path,
            launch,
            report_plan,
            verified_root,
        )
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
        "input_packet_sha256": sha256(input_packet_bytes),
        "input_packet_bytes_base64": base64.b64encode(input_packet_bytes).decode("ascii"),
    }
    lease_path = state_root / "slots" / slot_id / "lease.json"
    agent_claim_path = state_root / "agents" / agent_id / "claim.json"
    root_claim_path = state_root / "attempt-roots" / f"{root_claim_id}.json"
    with operation_lock(state_root):
        leases = _authoritative_leases(
            state_root, production_reviewer_ids=production_reviewer_ids
        )
        existing = next((item for item in leases if item["slot_id"] == slot_id), None)
        recovering = existing is not None
        if existing is not None:
            comparable = (
                "agent_id",
                "launch_record_sha256",
                "attempt_root",
                "attempt_root_claim_sha256",
                "envelope_spec_sha256",
                "input_packet_sha256",
            )
            if any(existing[field] != lease[field] for field in comparable):
                raise LeaseAlreadyExists(
                    f"slot {slot_id} already has a different started lease"
                )
            lease = existing
        else:
            if any(item["agent_id"] == agent_id for item in leases):
                raise LeaseAlreadyExists(
                    f"agent {agent_id} already has an authoritative attempt lease"
                )
            if any(item["attempt_root_claim_sha256"] == root_claim_id for item in leases):
                raise LeaseAlreadyExists("attempt root already has an authoritative lease")
            if agent_claim_path.exists() or root_claim_path.exists():
                raise ProtocolError("orphan uniqueness claim exists without an authoritative lease")
            if attempt_root.exists():
                raise LeaseAlreadyExists("attempt root is not fresh")
            try:
                exclusive_write(lease_path, canonical_json_bytes(lease))
            except FileExistsError as error:
                raise LeaseAlreadyExists("slot lease CAS was lost") from error
            os.chmod(lease_path, 0o400)
            fsync_directory(lease_path.parent)
        maybe_inject_fault(fault_after, "lease-cas")
        failure_path = state_root / "slots" / slot_id / "lease-failure.json"
        if failure_path.exists():
            raise ProtocolError("lease initialization has an immutable failure ledger")
        claim = {
            "schema_version": 1,
            "slot_id": slot_id,
            "agent_id": agent_id,
            "attempt_root": str(attempt_root),
            "launch_record_sha256": lease["launch_record_sha256"],
            "lease_sha256": sha256(canonical_json_bytes(lease)),
        }
        try:
            if not attempt_root.exists():
                os.mkdir(attempt_root, mode=0o700)
            elif (
                not recovering
                or not attempt_root.is_dir()
                or attempt_root.is_symlink()
            ):
                raise ProtocolError("lease-bound attempt root is not recoverable")
            maybe_inject_fault(fault_after, "attempt-root")
            _write_or_validate_immutable(agent_claim_path, claim)
            maybe_inject_fault(fault_after, "agent-claim")
            _write_or_validate_immutable(root_claim_path, claim)
            maybe_inject_fault(fault_after, "root-claim")
            ready = {
                "schema_version": 1,
                "status": "LEASE-READY",
                "slot_id": slot_id,
                "attempt_id": lease["attempt_id"],
                "lease_sha256": sha256(canonical_json_bytes(lease)),
                "agent_claim_sha256": sha256(canonical_json_bytes(claim)),
                "attempt_root_claim_sha256": root_claim_id,
            }
            _write_or_validate_immutable(
                state_root / "slots" / slot_id / "lease-ready.json", ready
            )
            maybe_inject_fault(fault_after, "ready")
        except InjectedFault:
            raise
        except BaseException as error:
            failure = {
                "schema_version": 1,
                "status": "LEASE-FAILED",
                "slot_id": slot_id,
                "attempt_id": lease["attempt_id"],
                "lease_sha256": sha256(canonical_json_bytes(lease)),
                "error_type": type(error).__name__,
            }
            try:
                _write_or_validate_immutable(failure_path, failure)
            except BaseException:
                pass
            raise
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


def semantic_output_errors(lease: dict[str, Any], output_bytes: bytes | None) -> list[str]:
    """Validate the declared primary output against its exact launch-bound packet."""

    if output_bytes is None:
        return ["semantic:declared-primary-output-unavailable"]
    launch = load_bound_launch(lease)
    role = launch["role"]
    try:
        if role == "report":
            output_bytes.decode("utf-8", errors="strict")
            return []
        output = strict_json_loads(output_bytes, f"{role} primary output")
        input_packet = load_bound_input_packet(lease)
        if role == "scorer":
            packet = validate_score_input_packet(
                input_packet, launch["mode"], launch["assignment_id"].rsplit("-", 1)[1]
            )
            tree = packet["packet_tree"]
            atoms = packet_json_file(tree, packet["resource_paths"]["atom_manifest"])
            rules = packet_json_file(tree, packet["resource_paths"]["defect_rules"])
            validate_direct_score(
                output,
                atoms,
                rules,
                launch["assignment_id"].rsplit("-", 1)[1],
                packet,
            )
        elif role == "consistency":
            packet = validate_consistency_packet(input_packet)
            tree = packet["packet_tree"]
            atoms = packet_json_file(tree, "resources/atom-manifest.json")
            rules = packet_json_file(tree, "resources/defect-rules.json")
            validate_consistency(
                output,
                atoms,
                rules,
                packet,
                launch["assignment_id"].rsplit("-", 1)[1],
            )
        elif role == "adjudicator":
            validate_adjudication(output, validate_adjudication_packet(input_packet))
        elif role == "materiality-reviewer":
            validate_materiality_review(
                output,
                validate_materiality_review_packet(input_packet, "READY"),
                launch["assignment_id"],
                "READY",
            )
        elif role == "materiality-adjudicator":
            validate_materiality_adjudication(
                output,
                validate_materiality_adjudication_packet(input_packet, "READY"),
                "READY",
            )
        else:  # pragma: no cover - validate_launch_record makes this unreachable.
            raise ProtocolError(f"unsupported semantic role: {role}")
    except (ProtocolError, UnicodeDecodeError) as error:
        return [f"semantic:{type(error).__name__}:{error}"]
    return []


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

    launch = load_bound_launch(lease)
    primary = scanned_by_path.get(launch["output_path"])
    semantic_errors = semantic_output_errors(
        lease,
        primary["data"] if primary is not None and primary["kind"] == "file" else None,
    )

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
        "semantic_errors": semantic_errors,
        "semantic_valid": not semantic_errors,
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
            "semantic_valid",
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
            "envelope_sha256",
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
        or type(pointer["semantic_valid"]) is not bool
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
        or terminal_claim["envelope_sha256"] != pointer["envelope_sha256"]
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
            "semantic_errors",
            "semantic_valid",
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
    primary_record = file_records.get(launch["output_path"])
    primary_bytes = None
    if primary_record is not None:
        primary_bytes = (
            object_path
            / "payload"
            / "output"
            / Path(*PurePosixPath(launch["output_path"]).parts)
        ).read_bytes()
    expected_semantic_errors = semantic_output_errors(lease, primary_bytes)
    if (
        envelope["semantic_errors"] != expected_semantic_errors
        or type(envelope["semantic_valid"]) is not bool
        or envelope["semantic_valid"] is not (not expected_semantic_errors)
        or pointer["semantic_valid"] is not envelope["semantic_valid"]
    ):
        raise ProtocolError("envelope semantic result disagrees with recomputation")
    if launch["role"] == "report" and launch["output_path"] not in declared:
        raise ProtocolError("bound report output is absent from envelope declaration")
    return envelope


def validate_terminal_claim(value: Any, lease: dict[str, Any]) -> dict[str, Any]:
    claim = require_exact_keys(
        value,
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
            "envelope_sha256",
        },
        "terminal claim",
    )
    if (
        claim["schema_version"] != 1
        or claim["status"] != "TERMINAL-CLAIMED"
        or claim["slot_id"] != lease["slot_id"]
        or claim["attempt_id"] != lease["attempt_id"]
        or claim["agent_id"] != lease["agent_id"]
        or claim["lease_sha256"] != sha256(canonical_json_bytes(lease))
        or claim["attempt_root"] != lease["attempt_root"]
        or (
            claim["final_response_sha256"] is not None
            and (
                not isinstance(claim["final_response_sha256"], str)
                or not HEX64.fullmatch(claim["final_response_sha256"])
            )
        )
        or not isinstance(claim["process_disposition"], str)
        or not claim["process_disposition"]
        or (
            claim["process_exit_code"] is not None
            and type(claim["process_exit_code"]) is not int
        )
        or not isinstance(claim["metadata_sha256"], str)
        or not HEX64.fullmatch(claim["metadata_sha256"])
        or not isinstance(claim["envelope_sha256"], str)
        or not HEX64.fullmatch(claim["envelope_sha256"])
    ):
        raise ProtocolError("terminal claim identity/content binding is invalid")
    return claim


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
    *,
    fault_after: str | None = None,
    static_root: Path | None = None,
    external_commitment_path: Path | None = None,
    test_capability: object | None = None,
) -> dict[str, Any]:
    state_root, _verified_root, production_reviewer_ids = require_state_context(
        state_root,
        static_root=static_root,
        external_commitment_path=external_commitment_path,
        test_capability=test_capability,
    )
    attempt_root = require_external_path(attempt_root, "attempt output root")
    slot_id = require_safe_id(slot_id, "slot ID")
    agent_id = require_safe_id(agent_id, "agent ID")
    if production_reviewer_ids is not None:
        agent_id = require_production_runtime_actor(
            agent_id, "production agent ID", production_reviewer_ids
        )
    if not isinstance(lease_token, str) or not re.fullmatch(r"[0-9a-f]{64}", lease_token):
        raise ProtocolError("invalid lease token")
    if not isinstance(metadata, dict):
        raise ProtocolError("coordinator metadata must be an object")
    lease_path = state_root / "slots" / slot_id / "lease.json"
    canonical_path = state_root / "slots" / slot_id / "canonical.json"
    terminal_claim_path = state_root / "slots" / slot_id / "terminal-claim.json"
    seal_failure_path = state_root / "slots" / slot_id / "seal-failure.json"
    with operation_lock(state_root):
        _authoritative_leases(
            state_root, production_reviewer_ids=production_reviewer_ids
        )
        if canonical_path.exists():
            raise CanonicalAlreadySealed(f"slot {slot_id} already has a canonical first-terminal envelope")
        if not lease_path.is_file():
            raise ProtocolError(f"slot {slot_id} has no started lease")
        lease = validate_lease(read_json(lease_path))
        if production_reviewer_ids is not None:
            require_production_runtime_actor(
                lease["agent_id"],
                "persisted production lease agent ID",
                production_reviewer_ids,
            )
        ready_path = state_root / "slots" / slot_id / "lease-ready.json"
        ready = require_exact_keys(
            read_json(ready_path) if ready_path.is_file() and not ready_path.is_symlink() else None,
            {
                "schema_version",
                "status",
                "slot_id",
                "attempt_id",
                "lease_sha256",
                "agent_claim_sha256",
                "attempt_root_claim_sha256",
            },
            "lease readiness ledger",
        )
        if (
            ready["schema_version"] != 1
            or ready["status"] != "LEASE-READY"
            or ready["slot_id"] != slot_id
            or ready["attempt_id"] != lease["attempt_id"]
            or ready["lease_sha256"] != sha256(canonical_json_bytes(lease))
            or ready["agent_claim_sha256"]
            != sha256(
                canonical_json_bytes(
                    {
                        "schema_version": 1,
                        "slot_id": slot_id,
                        "agent_id": lease["agent_id"],
                        "attempt_root": lease["attempt_root"],
                        "launch_record_sha256": lease["launch_record_sha256"],
                        "lease_sha256": sha256(canonical_json_bytes(lease)),
                    }
                )
            )
            or ready["attempt_root_claim_sha256"]
            != lease["attempt_root_claim_sha256"]
            or ready_path.lstat().st_mode & 0o222
        ):
            raise ProtocolError("lease is not crash-consistently ready")
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
        objects = state_root / "objects" / "sha256"
        objects.mkdir(parents=True, exist_ok=True)
        seal_request = {
            "lease_sha256": sha256(canonical_json_bytes(lease)),
            "final_response_sha256": (
                sha256(final_response) if final_response is not None else None
            ),
            "process_disposition": process_disposition,
            "process_exit_code": process_exit_code,
            "metadata_sha256": sha256(canonical_json_bytes(metadata)),
        }
        request_id = sha256(canonical_json_bytes(seal_request))[:24]
        stage = objects / f".stage-{lease['attempt_id']}-{request_id}"
        terminal_claim: dict[str, Any]
        manifest: dict[str, Any]
        try:
            if terminal_claim_path.exists():
                if seal_failure_path.exists():
                    raise TerminalAlreadyClaimed(
                        f"slot {slot_id} has an immutable failed terminal transition"
                    )
                terminal_claim = require_exact_keys(
                    read_json(terminal_claim_path),
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
                        "envelope_sha256",
                    },
                    "terminal claim",
                )
                expected_terminal_fields = {
                    "schema_version": 1,
                    "status": "TERMINAL-CLAIMED",
                    "slot_id": slot_id,
                    "attempt_id": lease["attempt_id"],
                    "agent_id": agent_id,
                    "lease_sha256": sha256(canonical_json_bytes(lease)),
                    "attempt_root": lease["attempt_root"],
                    "final_response_sha256": (
                        sha256(final_response) if final_response is not None else None
                    ),
                    "process_disposition": process_disposition,
                    "process_exit_code": process_exit_code,
                    "metadata_sha256": sha256(canonical_json_bytes(metadata)),
                }
                if any(
                    terminal_claim.get(key) != value
                    for key, value in expected_terminal_fields.items()
                ):
                    raise TerminalAlreadyClaimed(
                        f"slot {slot_id} terminal recovery arguments do not match the claim"
                    )
                digest = terminal_claim["envelope_sha256"]
                if not isinstance(digest, str) or not HEX64.fullmatch(digest):
                    raise ProtocolError("terminal claim envelope digest is invalid")
            else:
                if seal_failure_path.exists():
                    raise ProtocolError("seal-failure ledger exists without terminal claim")
                if stage.exists():
                    if not stage.is_dir() or stage.is_symlink():
                        raise ProtocolError("seal recovery stage is not a regular directory")
                    digest = byte_tree_digest(stage)
                    manifest = read_json(stage / "envelope.json")
                    harden_tree_read_only(stage)
                else:
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
                    fsync_directory(objects)
                terminal_claim = {
                    "schema_version": 1,
                    "status": "TERMINAL-CLAIMED",
                    "slot_id": slot_id,
                    "attempt_id": lease["attempt_id"],
                    "agent_id": agent_id,
                    "lease_sha256": sha256(canonical_json_bytes(lease)),
                    "attempt_root": lease["attempt_root"],
                    "final_response_sha256": (
                        sha256(final_response) if final_response is not None else None
                    ),
                    "process_disposition": process_disposition,
                    "process_exit_code": process_exit_code,
                    "metadata_sha256": sha256(canonical_json_bytes(metadata)),
                    "envelope_sha256": digest,
                }
                exclusive_write(terminal_claim_path, canonical_json_bytes(terminal_claim))
                os.chmod(terminal_claim_path, 0o400)
                fsync_directory(terminal_claim_path.parent)
            maybe_inject_fault(fault_after, "terminal-claim")
            object_path = objects / digest
            if object_path.exists():
                if (
                    not object_path.is_dir()
                    or object_path.is_symlink()
                    or byte_tree_digest(object_path) != digest
                ):
                    raise ProtocolError(f"pre-existing envelope object is invalid: {digest}")
            else:
                if (
                    not stage.is_dir()
                    or stage.is_symlink()
                    or byte_tree_digest(stage) != digest
                ):
                    raise ProtocolError("terminal claim lacks its immutable recovery stage")
                os.rename(stage, object_path)
                fsync_directory(objects)
            maybe_inject_fault(fault_after, "object-publish")
            manifest = read_json(object_path / "envelope.json")
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
                "semantic_valid": manifest["semantic_valid"],
            }
            semantic_verify_envelope(object_path, lease, pointer, terminal_claim)
            try:
                exclusive_write(canonical_path, canonical_json_bytes(pointer))
            except FileExistsError as error:
                raise CanonicalAlreadySealed(f"slot {slot_id} lost the first-terminal CAS") from error
        except InjectedFault:
            raise
        except BaseException as error:
            if not terminal_claim_path.exists():
                raise
            claimed = read_json(terminal_claim_path)
            failure = {
                "schema_version": 1,
                "status": "SEAL-FAILED",
                "slot_id": slot_id,
                "attempt_id": lease["attempt_id"],
                "terminal_claim_sha256": sha256(canonical_json_bytes(claimed)),
                "error_type": type(error).__name__,
            }
            try:
                _write_or_validate_immutable(seal_failure_path, failure)
            except BaseException:
                pass
            raise
        os.chmod(canonical_path, 0o400)
        os.chmod(canonical_path.parent, 0o500)
        fsync_directory(canonical_path.parent)
        fsync_directory(canonical_path.parent.parent)
        maybe_inject_fault(fault_after, "canonical-pointer")
    return pointer


def _validate_claim_inventory(
    root: Path,
    expected: dict[Path, dict[str, Any]],
    *,
    nested: bool,
    label: str,
) -> None:
    if not root.exists():
        return
    if not root.is_dir() or root.is_symlink():
        raise ProtocolError(f"{label} claim root is not a regular directory")
    actual: list[Path] = []
    if nested:
        for directory in sorted(root.iterdir(), key=lambda item: item.name):
            if not directory.is_dir() or directory.is_symlink():
                raise ProtocolError(f"{label} claim root contains a non-directory entry")
            require_safe_id(directory.name, f"{label} claim directory")
            entries = list(directory.iterdir())
            if any(item.name != "claim.json" for item in entries):
                raise ProtocolError(f"{label} claim directory contains an unexpected entry")
            actual.extend(item for item in entries if item.name == "claim.json")
    else:
        actual = list(root.iterdir())
        if any(
            not item.is_file()
            or item.is_symlink()
            or re.fullmatch(r"[0-9a-f]{64}\.json", item.name) is None
            for item in actual
        ):
            raise ProtocolError(f"{label} claim root contains an invalid entry")
    for path in actual:
        if (
            path not in expected
            or not path.is_file()
            or path.is_symlink()
            or path.lstat().st_mode & 0o222
            or read_json(path) != expected[path]
        ):
            raise ProtocolError(f"unexpected or invalid {label} uniqueness claim: {path}")


def verify_state(
    state_root: Path,
    *,
    static_root: Path | None = None,
    external_commitment_path: Path | None = None,
    test_capability: object | None = None,
) -> dict[str, Any]:
    state_root, _verified_root, production_reviewer_ids = require_state_context(
        state_root,
        static_root=static_root,
        external_commitment_path=external_commitment_path,
        test_capability=test_capability,
    )
    if not state_root.exists():
        return {"schema_version": 1, "state_valid": True, "complete": False, "staging_entries": [], "slots": []}
    if not state_root.is_dir() or state_root.is_symlink():
        raise ProtocolError("protocol state root is not a regular directory")
    with operation_lock(state_root):
        return _verify_state_locked(
            state_root, production_reviewer_ids=production_reviewer_ids
        )


def _verify_state_locked(
    state_root: Path,
    *,
    production_reviewer_ids: frozenset[str] | None = None,
) -> dict[str, Any]:
    allowed_root_names = {
        ".protocol.lock",
        "slots",
        "agents",
        "attempt-roots",
        "objects",
        "aggregation",
    }
    unexpected_root = {path.name for path in state_root.iterdir()} - allowed_root_names
    if unexpected_root:
        raise ProtocolError(
            f"unexpected protocol state entries: {sorted(unexpected_root)}"
        )
    aggregation_root = state_root / "aggregation"
    if aggregation_root.exists():
        if not aggregation_root.is_dir() or aggregation_root.is_symlink():
            raise ProtocolError("aggregation state root is not a regular directory")
        allowed_aggregation_names = {
            "inputs",
            "derived",
            "integration-receipts",
            "aggregate-context.json",
        }
        unexpected_aggregation = {
            path.name for path in aggregation_root.iterdir()
        } - allowed_aggregation_names
        if unexpected_aggregation:
            raise ProtocolError(
                "unexpected aggregation state entries: "
                f"{sorted(unexpected_aggregation)}"
            )
        for path in aggregation_root.rglob("*"):
            if path.is_symlink() or not (path.is_dir() or path.is_file()):
                raise ProtocolError(f"unsupported aggregation state entry: {path}")
    slots_root = state_root / "slots"
    results: list[dict[str, Any]] = []
    if slots_root.exists() and (not slots_root.is_dir() or slots_root.is_symlink()):
        raise ProtocolError("slots ledger root is not a regular directory")
    expected_agent_claims: dict[Path, dict[str, Any]] = {}
    expected_root_claims: dict[Path, dict[str, Any]] = {}
    referenced_objects: set[str] = set()
    slot_paths = (
        sorted(slots_root.iterdir(), key=lambda path: path.name)
        if slots_root.exists()
        else []
    )
    if aggregation_root.exists() and not slot_paths:
        raise ProtocolError("aggregation state exists without any authoritative attempt slots")
    for slot_path in slot_paths:
        if not slot_path.is_dir() or slot_path.is_symlink():
            raise ProtocolError("slots ledger contains a non-directory entry")
        slot_id = require_safe_id(slot_path.name, "slot directory")
        allowed_names = {
            "lease.json",
            "lease-ready.json",
            "lease-failure.json",
            "terminal-claim.json",
            "canonical.json",
            "seal-failure.json",
        }
        unexpected = {path.name for path in slot_path.iterdir()} - allowed_names
        if unexpected:
            raise ProtocolError(f"unexpected slot ledger entries for {slot_id}: {sorted(unexpected)}")
        lease_path = slot_path / "lease.json"
        if not lease_path.is_file() or lease_path.is_symlink():
            raise ProtocolError(f"slot {slot_id} lacks a regular lease ledger")
        lease = validate_lease(read_json(lease_path))
        if production_reviewer_ids is not None:
            require_production_runtime_actor(
                lease["agent_id"],
                "persisted production lease agent ID",
                production_reviewer_ids,
            )
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
            "lease_sha256": sha256(canonical_json_bytes(lease)),
        }
        root_claim_id = lease["attempt_root_claim_sha256"]
        claim_items = (
            (state_root / "agents" / lease["agent_id"] / "claim.json", "agent"),
            (state_root / "attempt-roots" / f"{root_claim_id}.json", "attempt-root"),
        )
        expected_agent_claims[claim_items[0][0]] = expected_claim
        expected_root_claims[claim_items[1][0]] = expected_claim
        ready_path = slot_path / "lease-ready.json"
        lease_failure_path = slot_path / "lease-failure.json"
        if lease_failure_path.exists():
            failure = require_exact_keys(
                read_json(lease_failure_path),
                {
                    "schema_version",
                    "status",
                    "slot_id",
                    "attempt_id",
                    "lease_sha256",
                    "error_type",
                },
                "lease failure",
            )
            if (
                failure["schema_version"] != 1
                or failure["status"] != "LEASE-FAILED"
                or failure["slot_id"] != slot_id
                or failure["attempt_id"] != lease["attempt_id"]
                or failure["lease_sha256"] != sha256(canonical_json_bytes(lease))
                or not isinstance(failure["error_type"], str)
                or not failure["error_type"]
                or lease_failure_path.is_symlink()
                or lease_failure_path.lstat().st_mode & 0o222
            ):
                raise ProtocolError(f"invalid lease-failure ledger for slot {slot_id}")
            if ready_path.exists():
                raise ProtocolError(f"slot {slot_id} has both ready and failed lease ledgers")
            results.append(
                {"slot_id": slot_id, "status": "LEASE_FAILED", "format_valid": False, "semantic_valid": False}
            )
            continue
        if not ready_path.exists():
            results.append(
                {"slot_id": slot_id, "status": "LEASE_INITIALIZING", "format_valid": False, "semantic_valid": False}
            )
            continue
        ready = require_exact_keys(
            read_json(ready_path),
            {
                "schema_version",
                "status",
                "slot_id",
                "attempt_id",
                "lease_sha256",
                "agent_claim_sha256",
                "attempt_root_claim_sha256",
            },
            "lease readiness ledger",
        )
        if (
            ready != {
                "schema_version": 1,
                "status": "LEASE-READY",
                "slot_id": slot_id,
                "attempt_id": lease["attempt_id"],
                "lease_sha256": sha256(canonical_json_bytes(lease)),
                "agent_claim_sha256": sha256(canonical_json_bytes(expected_claim)),
                "attempt_root_claim_sha256": root_claim_id,
            }
            or ready_path.is_symlink()
            or ready_path.lstat().st_mode & 0o222
        ):
            raise ProtocolError(f"invalid lease readiness ledger for slot {slot_id}")
        for claim_path, label in claim_items:
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
            results.append(
                {"slot_id": slot_id, "status": "STARTED", "format_valid": False, "semantic_valid": False}
            )
            continue
        if not terminal_path.is_file() or terminal_path.is_symlink() or terminal_path.lstat().st_mode & 0o222:
            raise ProtocolError(f"slot {slot_id} terminal claim is not immutable/regular")
        terminal_claim = validate_terminal_claim(read_json(terminal_path), lease)
        terminal_claim_digest = sha256(canonical_json_bytes(terminal_claim))
        referenced_objects.add(terminal_claim["envelope_sha256"])
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
                        "semantic_valid": False,
                    }
                )
            else:
                results.append(
                    {
                        "slot_id": slot_id,
                        "status": "TERMINAL_CLAIMED_INCOMPLETE",
                        "format_valid": False,
                        "semantic_valid": False,
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
        referenced_objects.add(digest)
        for path in (object_path, *object_path.rglob("*")):
            if path.lstat().st_mode & 0o222:
                raise ProtocolError(f"published envelope object is not read-only: {path}")
        envelope = semantic_verify_envelope(
            object_path, lease, pointer, terminal_claim
        )
        results.append(
            {
                "slot_id": slot_id,
                "status": "SEALED",
                "envelope_sha256": digest,
                "format_valid": envelope["format_valid"],
                "semantic_valid": envelope["semantic_valid"],
            }
        )
    _validate_claim_inventory(
        state_root / "agents", expected_agent_claims, nested=True, label="agent"
    )
    _validate_claim_inventory(
        state_root / "attempt-roots",
        expected_root_claims,
        nested=False,
        label="attempt-root",
    )
    objects_root = state_root / "objects" / "sha256"
    staging_entries: list[str] = []
    if objects_root.exists():
        if not objects_root.is_dir() or objects_root.is_symlink():
            raise ProtocolError("content-addressed object root is not a regular directory")
        published = {
            path.name
            for path in objects_root.iterdir()
            if path.is_dir() and not path.is_symlink() and HEX64.fullmatch(path.name)
        }
        unexpected_objects = published - referenced_objects
        if unexpected_objects:
            raise ProtocolError(
                f"unreferenced canonical envelope objects: {sorted(unexpected_objects)}"
            )
        unexpected_entries = {
            path.name
            for path in objects_root.iterdir()
            if path.name not in published and not path.name.startswith(".stage-")
        }
        if unexpected_entries:
            raise ProtocolError(
                f"unexpected content-addressed object entries: {sorted(unexpected_entries)}"
            )
        staging_entries = sorted(
            path.name for path in objects_root.iterdir() if path.name.startswith(".stage-")
        )
    complete = bool(results) and all(item["status"] == "SEALED" for item in results)
    state_valid = not staging_entries and all(
        item["status"] in ("STARTED", "SEALED")
        and (item["status"] != "SEALED" or (item["format_valid"] and item["semantic_valid"]))
        for item in results
    )
    return {
        "schema_version": 1,
        "state_valid": state_valid,
        "complete": complete,
        "staging_entries": staging_entries,
        "slots": results,
    }


def read_committed_json(path: Path, label: str) -> Any:
    if (
        not path.is_file()
        or path.is_symlink()
        or path.lstat().st_mode & 0o222
    ):
        raise ProtocolError(f"{label} must be an immutable regular file: {path}")
    return read_json(path)


def validate_aggregate_input_tree(static_root: Path) -> Path:
    input_root = static_root / "runtime" / "state" / "aggregation" / "inputs"
    if (
        input_root.is_symlink()
        or not input_root.is_dir()
        or input_root.lstat().st_mode & 0o222
    ):
        raise ProtocolError("aggregate input root must be an immutable real directory")
    expected = {
        "word-counts.json",
        "projection-audit-manifest.json",
        "scoring-bundle-manifest.json",
        "materiality-ledger.json",
        "final-scores",
    }
    actual = {path.name for path in input_root.iterdir()}
    if actual != expected:
        raise ProtocolError(
            f"aggregate input file set is not exact; missing={sorted(expected - actual)}, "
            f"extra={sorted(actual - expected)}"
        )
    final_root = input_root / "final-scores"
    if (
        final_root.is_symlink()
        or not final_root.is_dir()
        or final_root.lstat().st_mode & 0o222
    ):
        raise ProtocolError("final-score input root must be an immutable real directory")
    expected_finals = {f"{mode}.json" for mode in MODES}
    actual_finals = {path.name for path in final_root.iterdir()}
    if actual_finals != expected_finals:
        raise ProtocolError("final-score input file set is not exact")
    for path in input_root.rglob("*"):
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ProtocolError(f"aggregate input tree has an unsupported entry: {path}")
        if path.lstat().st_mode & 0o222:
            raise ProtocolError(f"aggregate input tree entry is mutable: {path}")
    return input_root


def load_verified_static_bundle(
    static_root: Path,
    external_commitment_path: Path | None = None,
) -> tuple[Path, dict[str, Any], frozenset[str]]:
    if (RUN / "STATIC-LOCK.json").exists():
        raise ProtocolError(
            "production operations must execute the trusted source protocol, "
            "not a protocol copy inside a candidate bundle"
        )
    lexical = Path(os.path.abspath(os.fspath(static_root)))
    if lexical.is_symlink() or not lexical.is_dir() or lexical.resolve() != lexical:
        raise ProtocolError(
            "bound aggregate static root must be an absolute normalized real directory"
        )
    root = lexical
    if external_commitment_path is None:
        raise ProtocolError(
            "production operation requires a separately custodied external commitment"
        )
    commitment_path = Path(
        os.path.abspath(os.fspath(external_commitment_path))
    )
    if (
        commitment_path.is_symlink()
        or not commitment_path.is_file()
        or is_within(commitment_path, root)
    ):
        raise ProtocolError(
            "external commitment must be a real file outside the candidate bundle"
        )
    commitment_bytes = commitment_path.read_bytes()
    commitment = strict_json_loads(
        commitment_bytes, "separately custodied external commitment"
    )
    if commitment_bytes != canonical_json_bytes(commitment):
        raise ProtocolError("external commitment must use canonical JSON bytes")
    try:
        integration = trusted_integration_module()
        verifier = integration.get("verify_static_with_reviewer_ids")
        if not callable(verifier):
            raise ProtocolError(
                "trusted integration lacks coherent static/reviewer verification"
            )
        verified = verifier(
            root,
            expected_bundle_kind="PRODUCTION",
            expected_external_commitment=commitment,
        )
    except Exception as error:
        raise ProtocolError("bound aggregate requires a valid static lock") from error
    for name in ("protocol.py", "integrate.py", "prepare.py", "word_count.py"):
        trusted_path = RUN / name
        candidate_path = root / name
        if (
            candidate_path.is_symlink()
            or not candidate_path.is_file()
            or candidate_path.read_bytes() != trusted_path.read_bytes()
        ):
            raise ProtocolError(
                f"verified static executable does not equal the trusted harness: {name}"
            )
    trusted_declaration = RUN / "static-inputs" / "source-declaration.json"
    candidate_declaration = root / "static" / "integration" / "source-declaration.json"
    if (
        trusted_declaration.is_symlink()
        or not trusted_declaration.is_file()
        or candidate_declaration.is_symlink()
        or not candidate_declaration.is_file()
        or candidate_declaration.read_bytes() != trusted_declaration.read_bytes()
    ):
        raise ProtocolError(
            "verified production bundle source declaration is not the trusted canonical selection"
        )
    lock_path = root / "STATIC-LOCK.json"
    if sha256(lock_path.read_bytes()) == "0" * 64:  # defensive impossible sentinel
        raise ProtocolError("static lock digest is the forbidden zero sentinel")
    if (
        not isinstance(verified, tuple)
        or len(verified) != 2
        or not isinstance(verified[0], dict)
        or not isinstance(verified[1], (set, frozenset))
    ):
        raise ProtocolError("trusted static verifier returned an invalid context")
    lock, raw_reviewer_ids = verified
    if len(raw_reviewer_ids) != 11:
        raise ProtocolError("locked reviewer identity set is not exactly eleven actors")
    reviewer_ids = frozenset(
        require_production_actor_id(value, "locked reviewer actor ID")
        for value in raw_reviewer_ids
    )
    return root, lock, reviewer_ids


def load_ready_generated_documents(static_root: Path) -> dict[str, Any]:
    generated_root = static_root / "static" / "generated"
    names = (
        "condition-map.json",
        "target-map.json",
        "launch-schedule.json",
        "blind-map.json",
        "presentation-orders.json",
        "scoring-schedule.json",
        "consistency-schedule.json",
        "randomization-commitments.json",
    )
    documents = {
        name: read_json(generated_root / name)
        for name in names
    }
    seeds = read_json(generated_root / "seeds.json")
    try:
        preparation = run_trusted_module("prepare.py", "v5_bound_prepare_verify")
        preparation["verify_generated"](
            documents, seeds, expected_status="READY"
        )
    except Exception as error:
        raise ProtocolError("bound aggregate generated documents do not regenerate") from error
    launches = [
        read_json(generated_root / "launch-records" / f"r{index:03d}.json")
        for index in range(1, 121)
    ]
    validate_schedule_launch_ids(documents["launch-schedule.json"], launches)
    documents["report-launch-records"] = launches
    execution_digests = {
        role: sha256(
            (static_root / "static" / "execution-manifests" / f"{role}.json").read_bytes()
        )
        for role in SEMANTIC_AGENT_ROLES
    }
    spec_digests = {
        role: sha256(
            (static_root / "static" / "envelope-specs" / f"{role}.json").read_bytes()
        )
        for role in SEMANTIC_AGENT_ROLES
        if role != "report"
    }
    try:
        integration = trusted_integration_module()
        declaration_path = (
            static_root / "static" / "integration" / "source-declaration.json"
        )
        declaration_bytes = declaration_path.read_bytes()
        reviewed_path = (
            static_root / "static" / "integration" / "integration-values.json"
        )
        reviewed = integration["validate_reviewed_values"](
            integration["parse_json_bytes"](
                reviewed_path.read_bytes(), str(reviewed_path)
            ),
            declaration_bytes,
        )
        packages = preparation["validate_packages"](
            read_json(static_root / "packages.json")
        )
        targets = preparation["validate_targets"](
            read_json(static_root / "targets.json")
        )
        report_spec_digests = {
            f"report-{mode}": sha256(
                (
                    static_root
                    / "static"
                    / "envelope-specs"
                    / f"report-{mode}.json"
                ).read_bytes()
            )
            for mode in MODES
        }
        integration["validate_report_material"](
            static_root,
            documents,
            packages,
            targets,
            reviewed,
            execution_digests,
            {**spec_digests, **report_spec_digests},
        )
        expected_contract, expected_prompts = integration[
            "derive_evaluator_material"
        ](static_root, documents, execution_digests, spec_digests)
    except Exception as error:
        raise ProtocolError(
            "report/evaluator launch contracts do not deterministically rederive"
        ) from error
    contract_path = generated_root / "evaluator-launch-contracts.json"
    contract_bytes = contract_path.read_bytes()
    actual_contract = strict_json_loads(contract_bytes, str(contract_path))
    if (
        actual_contract != expected_contract
        or contract_bytes != integration["pretty_json_bytes"](expected_contract)
    ):
        raise ProtocolError("evaluator launch contract is not the deterministic derivation")
    for path_text, expected_bytes in expected_prompts.items():
        prompt_path = static_root / Path(*PurePosixPath(path_text).parts)
        if (
            prompt_path.is_symlink()
            or not prompt_path.is_file()
            or prompt_path.read_bytes() != expected_bytes
        ):
            raise ProtocolError(f"evaluator prompt is not the deterministic rendering: {path_text}")
    documents["evaluator-launch-contracts"] = actual_contract
    return documents


def derive_blind_join(documents: dict[str, Any]) -> list[dict[str, Any]]:
    conditions = {
        row["condition_label"]: row["role"]
        for row in documents["condition-map.json"]["conditions"]
    }
    targets = {
        row["target_label"]: row["mode"]
        for row in documents["target-map.json"]["targets"]
    }
    blind: dict[tuple[str, str], str] = {}
    for mode, rows in documents["blind-map.json"]["modes"].items():
        for row in rows:
            key = (mode, row["run_id"])
            if key in blind:
                raise ProtocolError("blind map contains a duplicate mode/run mapping")
            blind[key] = row["label"]
    result: list[dict[str, Any]] = []
    for slot in documents["launch-schedule.json"]["slots"]:
        try:
            mode = targets[slot["target_label"]]
            condition = conditions[slot["condition_label"]]
            label = blind[(mode, slot["run_id"])]
        except KeyError as error:
            raise ProtocolError("generated maps do not close over the schedule") from error
        result.append(
            {
                "run_id": slot["run_id"],
                "cell_id": slot["cell_id"],
                "mode": mode,
                "label": label,
                "condition_role": condition,
                "replicate": slot["replicate"],
            }
        )
    expected_runs = [f"r{index:03d}" for index in range(1, 121)]
    if [row["run_id"] for row in result] != expected_runs:
        raise ProtocolError("blind join run order is not exactly r001 through r120")
    expected_cells = {
        (mode, condition, replicate)
        for mode in MODES
        for condition in ("v5", "v4", "no_skill")
        for replicate in range(1, 6)
    }
    if {
        (row["mode"], row["condition_role"], row["replicate"])
        for row in result
    } != expected_cells:
        raise ProtocolError("blind join does not cover the exact 8x3x5 design")
    if {
        (row["mode"], row["label"]) for row in result
    } != {(mode, label) for mode in MODES for label in LABELS}:
        raise ProtocolError("blind join does not map every mode to A through O exactly")
    return result


def load_canonical_attempt_inventory(
    static_root: Path,
    production_reviewer_ids: frozenset[str],
) -> dict[str, dict[str, Any]]:
    state_root = static_root / "runtime" / "state"
    if not state_root.is_dir() or state_root.is_symlink():
        raise ProtocolError("bound aggregate requires committed runtime/state")
    state_root = state_root.resolve()
    with operation_lock(state_root):
        state = _verify_state_locked(
            state_root, production_reviewer_ids=production_reviewer_ids
        )
        if state["staging_entries"]:
            raise ProtocolError("bound aggregate forbids incomplete envelope stages")
        leases = _authoritative_leases(
            state_root, production_reviewer_ids=production_reviewer_ids
        )
        attempts: dict[str, dict[str, Any]] = {}
        for lease in leases:
            launch = load_bound_launch(lease)
            assignment = launch["assignment_id"]
            if assignment in attempts:
                raise ProtocolError(f"duplicate canonical assignment: {assignment}")
            slot_path = state_root / "slots" / lease["slot_id"]
            canonical_path = slot_path / "canonical.json"
            terminal_path = slot_path / "terminal-claim.json"
            if not canonical_path.is_file() or not terminal_path.is_file():
                raise ProtocolError(f"assignment is not canonically sealed: {assignment}")
            pointer = read_json(canonical_path)
            terminal = read_json(terminal_path)
            object_path = (
                state_root / "objects" / "sha256" / pointer["envelope_sha256"]
            )
            envelope = semantic_verify_envelope(object_path, lease, pointer, terminal)
            primary_path = (
                object_path
                / "payload"
                / "output"
                / Path(*PurePosixPath(launch["output_path"]).parts)
            )
            primary = primary_path.read_bytes() if primary_path.is_file() else None
            attempts[assignment] = {
                "lease": lease,
                "launch": launch,
                "pointer": pointer,
                "envelope": envelope,
                "object_path": object_path,
                "primary_bytes": primary,
            }
    return attempts


def require_valid_evaluator_attempt(
    attempts: dict[str, dict[str, Any]],
    assignment: str,
    role: str,
    static_root: Path,
    documents: dict[str, Any],
) -> dict[str, Any]:
    attempt = attempts.get(assignment)
    if attempt is None:
        raise ProtocolError(f"missing canonical evaluator attempt: {assignment}")
    launch = attempt["launch"]
    if (
        launch["role"] != role
        or attempt["pointer"]["format_valid"] is not True
        or attempt["pointer"]["semantic_valid"] is not True
        or attempt["primary_bytes"] is None
    ):
        raise ProtocolError(f"invalid canonical evaluator attempt: {assignment}")
    packet_bytes = load_bound_input_packet_bytes(attempt["lease"])
    expected_launch, row = build_expected_evaluator_launch(
        static_root, documents, assignment, packet_bytes
    )
    if launch != expected_launch:
        raise ProtocolError(f"evaluator launch is not deterministically derived: {assignment}")
    verify_evaluator_input_tree(
        Path(launch["input_root"]), static_root, row, packet_bytes
    )
    return attempt


def attempt_output_json(attempt: dict[str, Any], label: str) -> Any:
    data = attempt["primary_bytes"]
    if not isinstance(data, bytes):
        raise ProtocolError(f"{label} lacks canonical primary output bytes")
    return strict_json_loads(data, label)


def reconstruct_final_scores(
    static_root: Path,
    attempts: dict[str, dict[str, Any]],
    projection_manifest: dict[str, Any],
    blind_join: list[dict[str, Any]],
    projected_reports: dict[tuple[str, str], bytes],
    scorer_receipts: dict[tuple[str, str], dict[str, Any]],
    documents: dict[str, Any],
) -> tuple[dict[str, dict[str, Any]], dict[str, Any], set[str]]:
    rules = validate_defect_rules(
        read_json(static_root / "freeze" / "rules" / "defect-rules.json"),
        "READY",
    )
    projection_by_mode_label = {
        (row["mode"], row["label"]): row
        for row in projection_manifest["records"]
    }
    run_by_mode_label = {
        (row["mode"], row["label"]): row for row in blind_join
    }
    final_root = (
        static_root
        / "runtime"
        / "state"
        / "aggregation"
        / "inputs"
        / "final-scores"
    )
    finals: dict[str, dict[str, Any]] = {}
    bundle_rows: list[dict[str, Any]] = []
    used_assignments: set[str] = set()
    for mode in MODES:
        atoms = validate_atom_manifest(
            read_json(static_root / "freeze" / "atoms" / f"{mode}.json"),
            mode,
            "READY",
        )
        scorer_attempts = [
            require_valid_evaluator_attempt(
                attempts,
                f"{mode}-{scorer}",
                "scorer",
                static_root,
                documents,
            )
            for scorer in SCORERS
        ]
        used_assignments.update(f"{mode}-{scorer}" for scorer in SCORERS)
        score_inputs = [load_bound_input_packet(item["lease"]) for item in scorer_attempts]
        direct_scores = [
            attempt_output_json(item, f"{mode} direct score {scorer}")
            for scorer, item in zip(SCORERS, scorer_attempts)
        ]
        for scorer, packet, score in zip(SCORERS, score_inputs, direct_scores):
            presentation = next(
                row["labels_in_order"]
                for row in documents["presentation-orders.json"]["presentations"]
                if row["claim"] == f"{mode}-{scorer}"
            )
            expected_packet = build_score_input_packet(
                mode,
                scorer,
                presentation,
                {
                    label: projected_reports[(mode, label)]
                    for label in LABELS
                },
                {
                    label: scorer_receipts[(mode, label)]
                    for label in LABELS
                },
                atoms,
                rules,
                (static_root / "freeze" / "oracle" / f"{mode}.md").read_bytes(),
                (static_root / "freeze" / "allowlists" / f"{mode}.txt").read_bytes(),
                (static_root / "freeze" / "authority" / "propositions.json").read_bytes(),
            )
            attempt = scorer_attempts[SCORERS.index(scorer)]
            packet = require_exact_score_input_packet(
                packet,
                expected_packet,
                mode,
                scorer,
                raw_bytes=load_bound_input_packet_bytes(attempt["lease"]),
            )
            validate_direct_score(score, atoms, rules, scorer, packet)
            report_index_by_label = {row["label"]: row for row in packet["reports"]}
            for label in LABELS:
                audit = projection_by_mode_label[(mode, label)]["receipt"]
                packet_report = report_index_by_label[label]
                if (
                    packet_report["projected_report_sha256"]
                    != audit["projected_report_sha256"]
                    or packet_file_bytes(
                        packet["packet_tree"],
                        packet_report["projected_report_path"],
                    )
                    != projected_reports[(mode, label)]
                    or packet_report["gh12_forced_present"]
                    is not bool(audit["replacements"])
                ):
                    raise ProtocolError(
                        f"scorer packet/projection audit mismatch: {mode}/{scorer}/{label}"
                    )
                run = run_by_mode_label[(mode, label)]
                if projection_by_mode_label[(mode, label)]["run_id"] != run["run_id"]:
                    raise ProtocolError("projection audit/blind join run mismatch")
        consistency_attempts = [
            require_valid_evaluator_attempt(
                attempts,
                f"{mode}-{reviewer}",
                "consistency",
                static_root,
                documents,
            )
            for reviewer in CONSISTENCY_REVIEWERS
        ]
        used_assignments.update(
            f"{mode}-{reviewer}" for reviewer in CONSISTENCY_REVIEWERS
        )
        consistency_inputs = [
            load_bound_input_packet(item["lease"]) for item in consistency_attempts
        ]
        if consistency_inputs[0] != consistency_inputs[1]:
            raise ProtocolError(f"consistency reviewers did not receive byte-equal input: {mode}")
        consistency_packet = validate_consistency_packet(consistency_inputs[0])
        tree = consistency_packet["packet_tree"]
        evidence = packet_file_bytes(tree, "resources/evidence-packet.bin")
        rebuilt_consistency = build_consistency_packet(
            direct_scores[0],
            direct_scores[1],
            score_inputs[0],
            score_inputs[1],
            atoms,
            rules,
            evidence,
        )
        if consistency_packet != rebuilt_consistency:
            raise ProtocolError(f"consistency input is not deterministically derived: {mode}")
        consistency_outputs = [
            attempt_output_json(item, f"{mode} consistency {reviewer}")
            for reviewer, item in zip(CONSISTENCY_REVIEWERS, consistency_attempts)
        ]
        for reviewer, output in zip(CONSISTENCY_REVIEWERS, consistency_outputs):
            validate_consistency(output, atoms, rules, consistency_packet, reviewer)
        adjudication_packet = build_adjudication_packet(
            direct_scores[0],
            direct_scores[1],
            score_inputs[0],
            score_inputs[1],
            consistency_outputs[0],
            consistency_outputs[1],
            atoms,
            rules,
            evidence,
        )
        adjudication: dict[str, Any] | None
        adjudicator_envelope: str | None
        adjudication_bytes: bytes | None
        assignment = f"{mode}-a1"
        if adjudication_packet["cells"]:
            adjudicator = require_valid_evaluator_attempt(
                attempts, assignment, "adjudicator", static_root, documents
            )
            used_assignments.add(assignment)
            launch_packet = load_bound_input_packet(adjudicator["lease"])
            if launch_packet != adjudication_packet:
                raise ProtocolError(f"adjudicator packet is not deterministically derived: {mode}")
            adjudication = attempt_output_json(adjudicator, f"{mode} adjudication")
            validate_adjudication(adjudication, adjudication_packet)
            adjudication_bytes = adjudicator["primary_bytes"]
            adjudicator_envelope = adjudicator["pointer"]["envelope_sha256"]
        else:
            if assignment in attempts:
                raise ProtocolError(f"empty adjudication packet has an adjudicator attempt: {mode}")
            adjudication = None
            adjudication_bytes = None
            adjudicator_envelope = None
        rebuilt_final = merge_final_scores(
            direct_scores[0],
            direct_scores[1],
            score_inputs[0],
            score_inputs[1],
            consistency_outputs[0],
            consistency_outputs[1],
            atoms,
            rules,
            evidence,
            adjudication,
        )
        final_path = final_root / f"{mode}.json"
        final = validate_final_score(
            read_committed_json(final_path, f"{mode} final score"), atoms, rules
        )
        if final != rebuilt_final:
            raise ProtocolError(f"stored final score is not the deterministic merge: {mode}")
        finals[mode] = final
        bundle_rows.append(
            {
                "mode": mode,
                "score_input_packet_digests": [
                    item["lease"]["input_packet_sha256"] for item in scorer_attempts
                ],
                "direct_score_digests": [
                    sha256(item["primary_bytes"]) for item in scorer_attempts
                ],
                "consistency_input_packet_digest": consistency_attempts[0]["lease"][
                    "input_packet_sha256"
                ],
                "consistency_review_digests": [
                    sha256(item["primary_bytes"]) for item in consistency_attempts
                ],
                "adjudication_packet_digest": sha256(
                    canonical_json_bytes(adjudication_packet)
                ),
                "adjudication_digest": (
                    sha256(adjudication_bytes) if adjudication_bytes is not None else None
                ),
                "final_score_digest": sha256(final_path.read_bytes()),
                "scorer_launch_envelope_digests": [
                    item["pointer"]["envelope_sha256"] for item in scorer_attempts
                ],
                "consistency_launch_envelope_digests": [
                    item["pointer"]["envelope_sha256"]
                    for item in consistency_attempts
                ],
                "adjudicator_launch_envelope_digest": adjudicator_envelope,
            }
        )
    expected_bundle = {
        "schema_version": 1,
        "status": "BOUND",
        "modes": bundle_rows,
    }
    bundle_path = (
        static_root
        / "runtime"
        / "state"
        / "aggregation"
        / "inputs"
        / "scoring-bundle-manifest.json"
    )
    actual_bundle = validate_scoring_bundle_manifest(
        read_committed_json(bundle_path, "scoring bundle manifest")
    )
    if actual_bundle != expected_bundle:
        raise ProtocolError("scoring bundle manifest is not exactly recomputable")
    return finals, actual_bundle, used_assignments


def reconstruct_materiality_ledger(
    static_root: Path,
    attempts: dict[str, dict[str, Any]],
    scope_payloads: dict[str, Any],
    materiality_contract: dict[str, Any],
    documents: dict[str, Any],
) -> tuple[dict[str, Any], set[str]]:
    reviewer_attempts = [
        require_valid_evaluator_attempt(
            attempts,
            reviewer,
            "materiality-reviewer",
            static_root,
            documents,
        )
        for reviewer in MATERIALITY_REVIEWERS
    ]
    packets = [load_bound_input_packet(item["lease"]) for item in reviewer_attempts]
    if packets[0] != packets[1]:
        raise ProtocolError("materiality reviewers did not receive byte-equal input")
    expected_packet = build_materiality_review_packet(
        scope_payloads, materiality_contract, "READY"
    )
    if packets[0] != expected_packet:
        raise ProtocolError("materiality review packet does not contain the exact derived scope")
    reviews = [
        attempt_output_json(item, f"materiality review {reviewer}")
        for reviewer, item in zip(MATERIALITY_REVIEWERS, reviewer_attempts)
    ]
    for reviewer, review in zip(MATERIALITY_REVIEWERS, reviews):
        validate_materiality_review(review, expected_packet, reviewer, "READY")
    adjudication_packet = build_materiality_adjudication_packet(
        expected_packet, reviews[0], reviews[1], "READY"
    )
    used = set(MATERIALITY_REVIEWERS)
    if adjudication_packet["cells"]:
        adjudicator = require_valid_evaluator_attempt(
            attempts,
            "ma1",
            "materiality-adjudicator",
            static_root,
            documents,
        )
        used.add("ma1")
        if load_bound_input_packet(adjudicator["lease"]) != adjudication_packet:
            raise ProtocolError("materiality adjudicator input is not deterministically derived")
        adjudication = attempt_output_json(adjudicator, "materiality adjudication")
        validate_materiality_adjudication(
            adjudication, adjudication_packet, "READY"
        )
    else:
        if "ma1" in attempts:
            raise ProtocolError("empty materiality adjudication packet has an adjudicator")
        adjudication = None
    expected_ledger = merge_materiality_ledger(
        expected_packet, reviews[0], reviews[1], adjudication, "READY"
    )
    ledger_path = (
        static_root
        / "runtime"
        / "state"
        / "aggregation"
        / "inputs"
        / "materiality-ledger.json"
    )
    ledger = validate_materiality_ledger(
        read_committed_json(ledger_path, "materiality ledger")
    )
    if ledger != expected_ledger:
        raise ProtocolError("materiality ledger is not the deterministic review merge")
    return ledger, used


def readable_tree_snapshot(
    root: Path, *, exclude_top_level: set[str] | None = None
) -> dict[str, Any]:
    if not root.is_dir() or root.is_symlink():
        raise ProtocolError(f"readable snapshot root is not a real directory: {root}")
    excluded = exclude_top_level or set()
    records: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root)
        if relative.parts and relative.parts[0] in excluded:
            continue
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ProtocolError(f"unsupported readable snapshot entry: {relative}")
        if not path.is_file():
            continue
        data = path.read_bytes()
        try:
            content = data.decode("utf-8", errors="strict")
            encoding = "UTF8"
        except UnicodeDecodeError:
            content = base64.b64encode(data).decode("ascii")
            encoding = "BASE64"
        records.append(
            {
                "path": relative.as_posix(),
                "size": len(data),
                "sha256": sha256(data),
                "encoding": encoding,
                "content": content,
            }
        )
    return {"schema_version": 1, "status": "READABLE-SNAPSHOT", "files": records}


def derive_aggregate_context(
    static_root: Path, external_commitment_path: Path | None = None
) -> dict[str, Any]:
    """Derive every gate input from verified static and canonical runtime bytes."""

    root, static_lock, production_reviewer_ids = load_verified_static_bundle(
        static_root, external_commitment_path
    )
    inventory = validate_root_inventory(
        read_json(root / "root-inventory.json"), "READY"
    )
    gate_manifest = validate_gate_manifest(
        read_json(root / "gate-manifest.json"), inventory, "READY"
    )
    validate_aggregation_rules(
        read_json(root / "aggregation-rules.json"), gate_manifest, "READY"
    )
    validate_report_projection_contract(
        read_json(root / "report-projection-contract.json"), "READY"
    )
    materiality_contract = validate_materiality_contract(
        read_json(root / "materiality-review-contract.json"), "READY"
    )
    documents = load_ready_generated_documents(root)
    trusted_integration = trusted_integration_module()
    declaration_bytes = (
        root / "static" / "integration" / "source-declaration.json"
    ).read_bytes()
    reviewed = trusted_integration["validate_reviewed_values"](
        read_json(root / "static" / "integration" / "integration-values.json"),
        declaration_bytes,
    )
    packages_document = read_json(root / "packages.json")
    trusted_prepare = run_trusted_module("prepare.py", "v5_aggregate_prepare")
    trusted_prepare["validate_packages"](packages_document)
    blind_join = derive_blind_join(documents)
    attempts = load_canonical_attempt_inventory(root, production_reviewer_ids)
    by_run = {row["run_id"]: row for row in blind_join}
    report_attempts: dict[str, dict[str, Any]] = {}
    static_launches = {
        launch["run_id"]: launch for launch in documents["report-launch-records"]
    }
    for run_id in sorted(by_run):
        attempt = attempts.get(run_id)
        if (
            attempt is None
            or attempt["launch"]["role"] != "report"
            or attempt["launch"]["run_id"] != run_id
            or attempt["launch"]["mode"] != by_run[run_id]["mode"]
            or attempt["launch"] != static_launches[run_id]
            or attempt["primary_bytes"] is None
        ):
            raise ProtocolError(f"missing or mismatched canonical report attempt: {run_id}")
        report_attempts[run_id] = attempt

    input_root = validate_aggregate_input_tree(root)
    word_manifest_path = input_root / "word-counts.json"
    word_manifest = validate_word_count_manifest(
        read_committed_json(word_manifest_path, "word-count manifest")
    )
    word_by_run = {row["run_id"]: row["receipt"] for row in word_manifest["records"]}
    target_rows = {
        row["mode"]: row for row in documents["target-map.json"]["targets"]
    }
    counter = run_trusted_module("word_count.py", "v5_bound_word_counter")
    count_words = counter["count_words"]
    for run_id, attempt in report_attempts.items():
        receipt = word_by_run[run_id]
        raw = attempt["primary_bytes"]
        mode = by_run[run_id]["mode"]
        expected_count = count_words(raw)
        if receipt != {
            "schema_version": 1,
            "status": "COUNTED",
            "algorithm_id": "unicode-whitespace-runs-python-v1",
            "report_sha256": sha256(raw),
            "word_count": expected_count,
            "word_cap": target_rows[mode]["word_cap"],
            "valid": expected_count <= target_rows[mode]["word_cap"],
        }:
            raise ProtocolError(f"word-count receipt is not recomputable: {run_id}")

    projection_path = input_root / "projection-audit-manifest.json"
    projection_manifest = validate_projection_audit_manifest(
        read_committed_json(projection_path, "projection audit manifest")
    )
    projection_by_run = {row["run_id"]: row for row in projection_manifest["records"]}
    projected_reports: dict[tuple[str, str], bytes] = {}
    scorer_receipts: dict[tuple[str, str], dict[str, Any]] = {}
    for run_id, row in projection_by_run.items():
        joined = by_run[run_id]
        raw = report_attempts[run_id]["primary_bytes"]
        expected_inventory = derive_report_secret_inventory(
            root,
            report_attempts[run_id]["launch"],
            report_attempts[run_id]["lease"],
            reviewed,
            packages_document,
            target_rows[joined["mode"]],
        )
        if row["secret_inventory"] != expected_inventory:
            raise ProtocolError(f"projection secret inventory is not derived: {run_id}")
        projected, scorer_receipt, recomputed_audit = project_report_for_scorer(
            row["label"], raw, expected_inventory
        )
        if (
            row["mode"] != joined["mode"]
            or row["label"] != joined["label"]
            or row["receipt"]["raw_report_sha256"]
            != sha256(raw)
            or row["receipt"] != recomputed_audit
            or row["receipt"]["projected_report_sha256"] != sha256(projected)
        ):
            raise ProtocolError(f"projection audit does not bind raw report: {run_id}")
        projected_reports[(row["mode"], row["label"])] = projected
        scorer_receipts[(row["mode"], row["label"])] = scorer_receipt

    finals, scoring_bundle, scoring_assignments = reconstruct_final_scores(
        root,
        attempts,
        projection_manifest,
        blind_join,
        projected_reports,
        scorer_receipts,
        documents,
    )
    joined_reports: list[dict[str, Any]] = []
    for row in blind_join:
        final_report = next(
            item for item in finals[row["mode"]]["reports"] if item["label"] == row["label"]
        )
        audit = projection_by_run[row["run_id"]]["receipt"]
        gh12_present = "GH12" in final_report["hard_errors"]
        if gh12_present is not bool(audit["replacements"]):
            raise ProtocolError(
                f"GH12 does not equal projection redaction presence: {row['run_id']}"
            )
        raw = report_attempts[row["run_id"]]["primary_bytes"]
        try:
            raw_text = raw.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise ProtocolError(f"canonical report is not UTF-8: {row['run_id']}") from error
        joined_reports.append(
            {
                **row,
                "raw_report_sha256": sha256(raw),
                "raw_report": raw_text,
                "projected_report_sha256": audit["projected_report_sha256"],
                "final_report": final_report,
            }
        )

    controls = validate_control_manifest(
        read_json(root / "freeze" / "controls.json"),
        "READY",
        root / "freeze" / "atoms",
    )
    candidate_by_mode: dict[str, list[dict[str, Any]]] = {
        mode: [
            row
            for row in joined_reports
            if row["mode"] == mode and row["condition_role"] == "v5"
        ]
        for mode in MODES
    }
    control_records: list[dict[str, Any]] = []
    for control in controls["controls"]:
        candidates = candidate_by_mode[control["mode"]]
        passed = all(
            all(
                next(atom for atom in row["final_report"]["atoms"] if atom["id"] == atom_id)[
                    "certificate_decision"
                ]
                == "PASS"
                for atom_id in control["atom_ids"]
            )
            for row in candidates
        )
        control_records.append(
            {
                "id": control["id"],
                "family": control["family"],
                "mode": control["mode"],
                "passed": passed,
                "candidate_run_ids": sorted(row["run_id"] for row in candidates),
            }
        )
    control_results = validate_control_results(
        {"schema_version": 1, "status": "DERIVED", "records": control_records},
        controls,
        "READY",
        root / "freeze" / "atoms",
    )

    lock_bytes = (root / "STATIC-LOCK.json").read_bytes()
    static_lock_sha = sha256(lock_bytes)
    rules_path = root / "aggregation-rules.json"
    rules_sha = sha256(rules_path.read_bytes())
    oracle_receipt_path = (
        root
        / "static"
        / "integration-receipts"
        / "H-VALIDATE-ORACLE-COVERAGE.json"
    )
    oracle_receipt = validate_integration_receipt(
        read_json(oracle_receipt_path),
        "H-VALIDATE-ORACLE-COVERAGE",
        "SNAPSHOT_REVIEW",
    )
    review_root = root / "freeze" / "reviews"
    oracle_reviews = [
        read_json(review_root / name)
        for name in ("oracle-review-1.json", "oracle-review-2.json")
    ]
    coherence_review = read_json(review_root / "coherence-review.json")
    for index, review in enumerate([*oracle_reviews, coherence_review]):
        review = require_exact_keys(
            review,
            {
                "schema_version",
                "status",
                "review_kind",
                "reviewer_id",
                "decision",
                "input_digests",
            },
            f"independent static review {index}",
        )
        if (
            review["schema_version"] != 1
            or review["status"] != "READY"
            or review["decision"] not in ("PASS", "FAIL")
            or not isinstance(review["reviewer_id"], str)
            or not review["reviewer_id"]
            or not isinstance(review["input_digests"], dict)
            or not review["input_digests"]
            or any(
                not isinstance(item, str) or not HEX64.fullmatch(item)
                for item in review["input_digests"].values()
            )
        ):
            raise ProtocolError("independent static review is invalid")

    candidate_package = packages_document["packages"]["v5"]
    if not isinstance(candidate_package, dict):
        raise ProtocolError("integrated bundle lacks the V5 candidate package")
    package_snapshot = readable_tree_snapshot(root / candidate_package["source_path"])
    harness_snapshot = readable_tree_snapshot(root, exclude_top_level={"runtime"})
    candidate_rows = [row for row in joined_reports if row["condition_role"] == "v5"]
    scope_payloads = {
        "V5_CANDIDATE_REPORTS": {
            "schema_version": 1,
            "status": "COMPLETE",
            "reports": candidate_rows,
        },
        "CANDIDATE_PACKAGE": {
            "schema_version": 1,
            "status": "CONTENT-BOUND",
            "identity": candidate_package,
            "tree": package_snapshot,
        },
        "HARNESS_PROTOCOL": {
            "schema_version": 1,
            "status": "STATIC-LOCKED",
            "static_lock_sha256": static_lock_sha,
            "tree": harness_snapshot,
        },
        "ADVERSARIAL_AND_COHERENCE_REVIEWS": {
            "schema_version": 1,
            "status": "COMPLETE",
            "oracle_reviews": oracle_reviews,
            "coherence_review": coherence_review,
        },
    }
    materiality_ledger, materiality_assignments = reconstruct_materiality_ledger(
        root, attempts, scope_payloads, materiality_contract, documents
    )
    allowed_assignments = set(report_attempts) | scoring_assignments | materiality_assignments
    if set(attempts) != allowed_assignments:
        raise ProtocolError(
            f"unexpected canonical assignments in aggregate state: {sorted(set(attempts) - allowed_assignments)}"
        )

    focused_recall = all(
        atom["certificate_decision"] == "PASS"
        for rows in candidate_by_mode.values()
        for row in rows
        for atom in row["final_report"]["atoms"]
    )
    proof_quality = all(
        row["passed"]
        for row in control_results["records"]
        if row["family"] == "PROOF_QUALITY"
    )
    classification_controls = all(
        row["passed"]
        for row in control_results["records"]
        if row["family"] == "CLASSIFICATION_CONTROL"
    )
    hard_error_count = sum(
        len(row["final_report"]["hard_errors"])
        for rows in candidate_by_mode.values()
        for row in rows
    )
    global_defect_count = sum(
        len(row["final_report"]["global_defects"])
        for rows in candidate_by_mode.values()
        for row in rows
    )
    comparison_pass = focused_recall
    for mode in MODES:
        atom_ids = [atom["id"] for atom in finals[mode]["reports"][0]["atoms"]]
        for atom_id in atom_ids:
            counts = {
                condition: sum(
                    next(
                        atom
                        for atom in row["final_report"]["atoms"]
                        if atom["id"] == atom_id
                    )["certificate_decision"]
                    == "PASS"
                    for row in joined_reports
                    if row["mode"] == mode and row["condition_role"] == condition
                )
                for condition in ("v5", "v4", "no_skill")
            }
            comparison_pass = comparison_pass and counts["v5"] >= counts["v4"] and counts[
                "v5"
            ] >= counts["no_skill"]

    invalid_output_count = sum(
        not (
            attempt["pointer"]["format_valid"]
            and attempt["pointer"]["semantic_valid"]
            and word_by_run[run_id]["valid"]
        )
        for run_id, attempt in report_attempts.items()
    )
    envelope_summary = [
        {
            "assignment_id": assignment,
            "role": attempt["launch"]["role"],
            "envelope_sha256": attempt["pointer"]["envelope_sha256"],
            "format_valid": attempt["pointer"]["format_valid"],
            "semantic_valid": attempt["pointer"]["semantic_valid"],
        }
        for assignment, attempt in sorted(attempts.items())
    ]
    atom_documents = {
        mode: read_json(root / "freeze" / "atoms" / f"{mode}.json") for mode in MODES
    }
    oracle_documents = {
        "coverage_receipt": oracle_receipt,
        "independent_reviews": oracle_reviews,
    }
    comparison_predicate = validate_comparison_predicate(
        read_json(root / "comparison-predicate.json"), "READY"
    )
    input_digests = {
        "schedule_slots_sha256": sha256(
            canonical_json_bytes(documents["launch-schedule.json"])
        ),
        "envelopes_sha256": sha256(canonical_json_bytes(envelope_summary)),
        "word_counts_sha256": sha256(canonical_json_bytes(word_manifest)),
        "atom_manifests_sha256": sha256(canonical_json_bytes(atom_documents)),
        "oracle_receipts_sha256": sha256(canonical_json_bytes(oracle_documents)),
        "blind_join_sha256": sha256(canonical_json_bytes(blind_join)),
        "joined_reports_sha256": sha256(canonical_json_bytes(joined_reports)),
        "projection_audit_manifest_sha256": sha256(
            canonical_json_bytes(projection_manifest)
        ),
        "scoring_bundle_manifest_sha256": sha256(
            canonical_json_bytes(scoring_bundle)
        ),
        "control_manifest_sha256": sha256(canonical_json_bytes(controls)),
        "control_results_sha256": sha256(canonical_json_bytes(control_results)),
        "materiality_ledger_sha256": sha256(
            canonical_json_bytes(materiality_ledger)
        ),
        "comparison_predicate_sha256": sha256(
            canonical_json_bytes(comparison_predicate)
        ),
        "coherence_review_sha256": sha256(canonical_json_bytes(coherence_review)),
    }
    core = {
        "schema_version": 1,
        "status": "DERIVED",
        "builder_id": AGGREGATE_BUILDER_ID,
        "static_lock_sha256": static_lock_sha,
        "rules_sha256": rules_sha,
        "input_digests": input_digests,
        "context": {
            "oracle": {
                "coverage_pass": all(
                    review["decision"] == "PASS" for review in oracle_reviews
                )
            },
            "collection": {
                "complete": len(report_attempts) == 120,
                "invalid_output_count": invalid_output_count,
            },
            "scores": {
                "focused_recall_pass": focused_recall,
                "proof_quality_pass": proof_quality,
                "controls_pass": classification_controls,
                "hard_error_count": hard_error_count,
                "global_defect_count": global_defect_count,
                "material_finding_count": sum(
                    finding["blocking"] for finding in materiality_ledger["findings"]
                ),
            },
            "comparison": {"predicate_pass": comparison_pass},
            "review": {"coherence_pass": coherence_review["decision"] == "PASS"},
        },
    }
    return validate_aggregate_context_document(
        {**core, "binding_sha256": sha256(canonical_json_bytes(core))}
    )


def verify_draft() -> None:
    previous = sys.dont_write_bytecode
    sys.dont_write_bytecode = True
    try:
        verify_preparation = runpy.run_path(
            str(RUN / "prepare.py"), run_name="v5_prepare_verify"
        )["verify_draft"]
        verify_preparation()
    finally:
        sys.dont_write_bytecode = previous
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
        "schemas/evaluator-launch-contracts.schema.json",
        "schemas/external-static-commitment.schema.json",
        "schemas/attempt-envelope.schema.json",
        "schemas/root-inventory.schema.json",
        "schemas/gate-manifest.schema.json",
        "schemas/gate-results.schema.json",
        "schemas/integration-hooks.schema.json",
        "schemas/integration-status.schema.json",
        "schemas/review-snapshot.schema.json",
        "schemas/static-lock.schema.json",
        "schemas/comparison-predicate.schema.json",
        "schemas/agent-authority-packet.schema.json",
        "schemas/aggregate-context.schema.json",
        "schemas/aggregation-rules.schema.json",
        "schemas/consistency-input-packet.schema.json",
        "schemas/control-manifest.schema.json",
        "schemas/control-results.schema.json",
        "schemas/fixture-manifest.schema.json",
        "schemas/launch-record.schema.json",
        "schemas/materiality-adjudication.schema.json",
        "schemas/materiality-adjudication-packet.schema.json",
        "schemas/materiality-ledger.schema.json",
        "schemas/materiality-review.schema.json",
        "schemas/materiality-review-contract.schema.json",
        "schemas/materiality-review-packet.schema.json",
        "schemas/mode-launch-prompt-set.schema.json",
        "schemas/packet-tree.schema.json",
        "schemas/lease.schema.json",
        "schemas/integration-receipt.schema.json",
        "schemas/report-projection-audit-receipt.schema.json",
        "schemas/projection-audit-manifest.schema.json",
        "schemas/report-projection-contract.schema.json",
        "schemas/report-projection-receipt.schema.json",
        "schemas/report-input-plan.schema.json",
        "schemas/report-secret-inventory.schema.json",
        "schemas/runtime-policy.schema.json",
        "schemas/score-input-packet.schema.json",
        "schemas/scoring-bundle-manifest.schema.json",
        "schemas/snapshot-review-contract.schema.json",
        "schemas/source-review-contract.schema.json",
        "schemas/source-review-receipt.schema.json",
        "schemas/source-review-snapshot.schema.json",
        "schemas/word-count-receipt.schema.json",
        "schemas/word-count-manifest.schema.json",
        "freeze/controls.json",
        "freeze/controls-completeness.md",
        "freeze/validate_controls.py",
        "freeze/validate_fixture_manifests.py",
        "freeze/validate_oracle_materials.py",
        "freeze/rules/defect-rules.json",
        "freeze/authority/propositions.json",
        "freeze/authority/quotation-locators.json",
        "freeze/authority/verification.json",
        "freeze/authority/validate_agent_visible.py",
        "freeze/authority/agent-visible/common.json",
        *(f"freeze/atoms/{mode}.json" for mode in MODES),
        *(f"freeze/fixtures/{mode}.json" for mode in MODES),
        *(f"freeze/oracle/{mode}.md" for mode in MODES),
        *(f"freeze/allowlists/{mode}.txt" for mode in MODES),
    }
    missing = sorted(name for name in required_files if not (RUN / name).is_file())
    if missing:
        raise ProtocolError(f"missing DRAFT harness files: {missing}")
    expected_schema_names = {
        Path(name).name for name in required_files if name.startswith("schemas/")
    }
    actual_schema_names = {
        path.name for path in (RUN / "schemas").iterdir() if path.is_file()
    }
    if actual_schema_names != expected_schema_names:
        raise ProtocolError(
            "schema inventory is not exact; "
            f"missing={sorted(expected_schema_names - actual_schema_names)}, "
            f"extra={sorted(actual_schema_names - expected_schema_names)}"
        )
    validate_integration_hooks(read_json(RUN / "integration-hooks.json"), "DRAFT")
    try:
        trusted_integration_module()["validate_runtime_policy"](
            RUN, expected_status="DRAFT"
        )
    except Exception as error:
        raise ProtocolError("DRAFT runtime policy is invalid") from error
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
        str(RUN / "freeze" / "validate_fixture_manifests.py"),
        run_name="v5_fixtures",
    )["main"]()
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
            "{{INPUT_PACKET_PATH}}",
            "{{SCORE_SCHEMA_PATH}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/consistency.md": {
            "{{REVIEWER_ID}}",
            "{{INPUT_PACKET_PATH}}",
            "{{CONSISTENCY_SCHEMA_PATH}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/adjudicator.md": {
            "{{INPUT_PACKET_PATH}}",
            "{{ADJUDICATION_SCHEMA_PATH}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/materiality-reviewer.md": {
            "{{REVIEWER_ID}}",
            "{{INPUT_PACKET_PATH}}",
            "{{REVIEW_SCHEMA_PATH}}",
            "{{OUTPUT_PATH}}",
        },
        "prompts/materiality-adjudicator.md": {
            "{{INPUT_PACKET_PATH}}",
            "{{ADJUDICATION_SCHEMA_PATH}}",
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
    schemas = {
        path.name: read_json(path)
        for path in sorted((RUN / "schemas").glob("*.json"))
    }
    schema_ids: dict[str, str] = {}
    for name, schema in schemas.items():
        if (
            not isinstance(schema, dict)
            or schema.get("$schema")
            != "https://json-schema.org/draft/2020-12/schema"
            or not isinstance(schema.get("$comment"), str)
            or not schema["$comment"].strip()
            or not isinstance(schema.get("$id"), str)
            or re.fullmatch(r"(?:urn:[A-Za-z0-9][A-Za-z0-9+.-]*:|https://)[^#]+", schema["$id"])
            is None
            or schema["$id"] in schema_ids
        ):
            raise ProtocolError(f"schema identity/DRAFT marker is invalid: {name}")
        schema_ids[schema["$id"]] = name

    def validate_schema_refs(value: Any, owner: str) -> None:
        if isinstance(value, dict):
            reference = value.get("$ref")
            if reference is not None:
                if not isinstance(reference, str):
                    raise ProtocolError(
                        f"schema has a non-string $ref: {owner}: {reference!r}"
                    )
                base, separator, fragment = reference.partition("#")
                local = base == "" and separator == "#" and (
                    fragment == "" or fragment.startswith("/")
                )
                known_external = base in schema_ids and (
                    not separator or fragment == "" or fragment.startswith("/")
                )
                if not (local or known_external):
                    raise ProtocolError(
                        f"schema has an unresolved or relative external $ref: {owner}: {reference!r}"
                    )
            for child in value.values():
                validate_schema_refs(child, owner)
        elif isinstance(value, list):
            for child in value:
                validate_schema_refs(child, owner)

    for name, schema in schemas.items():
        validate_schema_refs(schema, name)
    print("DRAFT protocol/static design validation passed")


def self_test() -> None:
    undefined_call_spelling = "trusted_" + "integrate("  # avoid matching this guard
    if undefined_call_spelling in (RUN / "protocol.py").read_text(encoding="utf-8"):
        raise AssertionError("protocol contains a call to the undefined trusted_integrate name")
    assert require_production_actor_id(
        "runtime-agent-0001", "synthetic production actor"
    ) == "runtime-agent-0001"
    for invalid_actor in (
        "short",
        "Runtime-Agent-0001",
        "runtime_agent_é0001",
        "runtime-agent-0001\n",
    ):
        try:
            require_production_actor_id(invalid_actor, "synthetic production actor")
        except ProtocolError:
            pass
        else:
            raise AssertionError(
                f"production actor grammar accepted an alias/control/Unicode value: {invalid_actor!r}"
            )
    try:
        reject_reviewer_runtime_reuse(
            "reviewer-actor-0001", frozenset({"reviewer-actor-0001"})
        )
    except ProtocolError:
        pass
    else:
        raise AssertionError("runtime eligibility accepted a locked reviewer identity")
    validate_report_projection_contract(read_json(RUN / "report-projection-contract.json"))
    projection_inventory = {
        "schema_version": 1,
        "status": "READY",
        "builder_id": PROJECTION_INVENTORY_BUILDER_ID,
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
        projected = {
            label: f"projected-{scorer}-{label}\n".encode() for label in LABELS
        }
        receipts = {
            label: {
                "schema_version": 1,
                "status": "PROJECTED",
                "label": label,
                "projected_report_sha256": sha256(projected[label]),
                "redaction_present": False,
                "replacement_count": 0,
            }
            for label in LABELS
        }
        return build_score_input_packet(
            "E",
            scorer,
            list(LABELS),
            projected,
            receipts,
            synthetic_atoms,
            synthetic_rules,
            b"synthetic oracle",
            b"synthetic allowlist",
            canonical_json_bytes({"synthetic": "authority"}),
        )

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
    altered_score_input = build_score_input_packet(
        "E",
        "s1",
        list(LABELS),
        {
            label: packet_file_bytes(
                score_input_first["packet_tree"], f"reports/{label}.md"
            )
            for label in LABELS
        },
        {
            label: packet_json_file(
                score_input_first["packet_tree"], f"receipts/{label}.json"
            )
            for label in LABELS
        },
        synthetic_atoms,
        synthetic_rules,
        b"substituted oracle",
        b"synthetic allowlist",
        canonical_json_bytes({"synthetic": "authority"}),
    )
    try:
        require_exact_score_input_packet(
            altered_score_input, score_input_first, "E", "s1"
        )
    except ProtocolError:
        pass
    else:
        raise AssertionError("a self-consistent substituted scorer oracle was accepted")
    extra_packet_file = copy.deepcopy(score_input_first)
    packet_files = {
        row["path"]: packet_file_bytes(extra_packet_file["packet_tree"], row["path"])
        for row in extra_packet_file["packet_tree"]["files"]
    }
    packet_files["undeclared/raw-report.md"] = b"secret raw report"
    extra_packet_file["packet_tree"] = build_packet_tree_manifest(
        "SCORER-INPUT", "E-s1-input", packet_files
    )
    try:
        validate_score_input_packet(extra_packet_file, "E", "s1")
    except ProtocolError:
        pass
    else:
        raise AssertionError("an undeclared scorer-packet file was accepted")
    score_input_second = synthetic_score_packet("s2")
    clean_first = synthetic_score("s1", score_input_first)
    clean_second = synthetic_score("s2", score_input_second)
    evidence_digest = b"synthetic evidence packet"
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
                b"stale synthetic evidence packet",
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
                b"stale synthetic evidence packet",
            ),
            "INVALID_ASSERTION",
        ),
        synthetic_atoms,
        synthetic_rules,
        b"stale synthetic evidence packet",
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

    materiality_packet = build_materiality_review_packet(
        {scope: {"synthetic_scope": scope} for scope in MATERIALITY_SCOPES}
    )

    def synthetic_materiality_review(
        reviewer: str, proposed_blocking: bool, include_finding: bool = True
    ) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "status": "MATERIALITY-REVIEW",
            "reviewer_id": reviewer,
            "input_packet_sha256": sha256(canonical_json_bytes(materiality_packet)),
            "scope_attestations": [
                {
                    "scope": scope,
                    "complete": True,
                    "evidence": f"Completed synthetic scope {scope}.",
                }
                for scope in MATERIALITY_SCOPES
            ],
            "findings": (
                [
                    {
                        "id": f"{reviewer}-F1",
                        "scope": "HARNESS_PROTOCOL",
                        "description": "Synthetic material protocol defect.",
                        "evidence": "Synthetic materiality evidence.",
                        "proposed_blocking": proposed_blocking,
                    }
                ]
                if include_finding
                else []
            ),
        }

    materiality_m1 = synthetic_materiality_review("m1", True)
    materiality_m2 = synthetic_materiality_review("m2", False)
    ready_materiality_contract = {
        **read_json(RUN / "materiality-review-contract.json"),
        "status": "READY",
    }
    ready_materiality_packet = build_materiality_review_packet(
        {scope: {"synthetic_scope": scope} for scope in MATERIALITY_SCOPES},
        ready_materiality_contract,
        "READY",
    )
    validate_materiality_review_packet(ready_materiality_packet, "READY")
    ready_m1 = {
        **copy.deepcopy(materiality_m1),
        "input_packet_sha256": sha256(canonical_json_bytes(ready_materiality_packet)),
    }
    ready_m2 = {
        **copy.deepcopy(materiality_m2),
        "input_packet_sha256": sha256(canonical_json_bytes(ready_materiality_packet)),
    }
    validate_materiality_review(ready_m1, ready_materiality_packet, "m1", "READY")
    validate_materiality_review(ready_m2, ready_materiality_packet, "m2", "READY")
    validate_materiality_adjudication_packet(
        build_materiality_adjudication_packet(
            ready_materiality_packet, ready_m1, ready_m2, "READY"
        ),
        "READY",
    )
    try:
        validate_materiality_review_packet(ready_materiality_packet, "DRAFT")
    except ProtocolError:
        pass
    else:
        raise AssertionError("READY materiality packet passed a DRAFT-only validator")
    materiality_adjudication_packet = build_materiality_adjudication_packet(
        materiality_packet, materiality_m1, materiality_m2
    )
    assert len(materiality_adjudication_packet["cells"]) == 1
    materiality_adjudication = {
        "schema_version": 1,
        "status": "ADJUDICATED",
        "packet_sha256": sha256(canonical_json_bytes(materiality_adjudication_packet)),
        "resolutions": [
            {
                "cell_id": materiality_adjudication_packet["cells"][0]["cell_id"],
                "decision": "BLOCKING",
                "evidence": "Synthetic inclusive-rule resolution.",
            }
        ],
    }
    materiality_ledger = merge_materiality_ledger(
        materiality_packet,
        materiality_m1,
        materiality_m2,
        materiality_adjudication,
    )
    assert materiality_ledger["scope_complete"] is True
    assert [item["blocking"] for item in materiality_ledger["findings"]] == [True]
    tampered_materiality = copy.deepcopy(materiality_packet)
    tampered_materiality["packet_tree"]["files"][0]["content"] += "tamper"
    try:
        validate_materiality_review_packet(tampered_materiality)
    except ProtocolError:
        pass
    else:
        raise AssertionError("tampered materiality packet content was accepted")
    for bad_json in ('{"a":1,"a":2}', '{"a":NaN}'):
        try:
            strict_json_loads(bad_json, "synthetic strict JSON")
        except ProtocolError:
            pass
        else:
            raise AssertionError("non-strict JSON was accepted")
    assert REPORT_RUN_ID.fullmatch("r001") and REPORT_RUN_ID.fullmatch("r120")
    assert all(
        REPORT_RUN_ID.fullmatch(value) is None
        for value in ("r1", "r000", "r121", "r0120")
    )

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
    assert gate_results["static_lock_sha256"] is None
    assert gate_results["aggregate_context_sha256"] is None
    by_gate = {row["id"]: row for row in gate_results["gates"]}
    assert by_gate["G-ISOLATION"]["direct_decision"] == "FAIL"
    assert by_gate["G-OUTPUT-FINALIZATION"]["direct_decision"] == "FAIL"
    assert by_gate["D-DIAGNOSTIC-COMPLETION"]["direct_decision"] == "PASS"
    assert by_gate["D-STATIC-INTEGRITY"]["direct_decision"] == "FAIL"
    assert by_gate["D-DIAGNOSTIC-COMPLETION"]["certificate_decision"] == "FAIL"
    assert "D-STATIC-INTEGRITY" in by_gate["D-DIAGNOSTIC-COMPLETION"]["root_failures"]
    assert inventory["release_eligibility"]["eligible"] is False
    weakened_gate = copy.deepcopy(gates)
    next(
        gate for gate in weakened_gate["gates"] if gate["id"] == "D-NO-HARD-ERROR"
    )["predicate"]["value"] = 999
    try:
        validate_gate_manifest(weakened_gate, inventory)
    except ProtocolError:
        pass
    else:
        raise AssertionError("a weakened hard-error gate threshold was accepted")
    ready_gates = {**copy.deepcopy(gates), "status": "READY"}
    ready_inventory = {**copy.deepcopy(inventory), "status": "READY"}
    locked_results = _evaluate_gate_context(
        ready_gates,
        ready_inventory,
        context,
        verified_bound_context=True,
        status="LOCKED-COMPUTED",
        context_trust="STATIC_LOCK_AND_DERIVED_AGGREGATE_BOUND",
        static_lock_sha256="a" * 64,
        aggregate_context_sha256="b" * 64,
        contract_status="READY",
    )
    locked_by_gate = {row["id"]: row for row in locked_results["gates"]}
    assert locked_by_gate["D-STATIC-INTEGRITY"]["direct_decision"] == "PASS"
    assert locked_by_gate["D-DIAGNOSTIC-COMPLETION"]["certificate_decision"] == "PASS"
    assert locked_by_gate["G-ISOLATION"]["direct_decision"] == "FAIL"
    assert locked_by_gate["G-OUTPUT-FINALIZATION"]["direct_decision"] == "FAIL"
    assert locked_results["release_eligibility"]["eligible"] is False
    aggregate_core = {
        "schema_version": 1,
        "status": "DERIVED",
        "builder_id": AGGREGATE_BUILDER_ID,
        "static_lock_sha256": "a" * 64,
        "rules_sha256": "c" * 64,
        "input_digests": {key: sha256(key.encode()) for key in AGGREGATE_DIGEST_KEYS},
        "context": context,
    }
    aggregate = validate_aggregate_context_document(
        {
            **aggregate_core,
            "binding_sha256": sha256(canonical_json_bytes(aggregate_core)),
        }
    )
    tampered_aggregate = copy.deepcopy(aggregate)
    tampered_aggregate["context"]["scores"]["focused_recall_pass"] = False
    try:
        validate_aggregate_context_document(tampered_aggregate)
    except ProtocolError:
        pass
    else:
        raise AssertionError("aggregate context tampering survived its binding digest")
    try:
        evaluate_bound_gates(RUN)
    except ProtocolError:
        pass
    else:
        raise AssertionError("unlocked DRAFT source masqueraded as a bound gate context")
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
        for alias in ("a//b", "a/./b", "a\\b"):
            try:
                require_relative_file(alias, "synthetic alias")
            except ProtocolError:
                pass
            else:
                raise AssertionError(f"noncanonical relative path was accepted: {alias!r}")
        readable_root = temporary_root / "readable-snapshot"
        readable_root.mkdir()
        (readable_root / "text.txt").write_text("readable text\n", encoding="utf-8")
        (readable_root / "binary.bin").write_bytes(b"\xff\x00")
        readable = readable_tree_snapshot(readable_root)
        readable_by_path = {row["path"]: row for row in readable["files"]}
        assert readable_by_path["text.txt"]["encoding"] == "UTF8"
        assert readable_by_path["binary.bin"]["encoding"] == "BASE64"
        (readable_root / "link").symlink_to(readable_root / "text.txt")
        try:
            readable_tree_snapshot(readable_root)
        except ProtocolError:
            pass
        else:
            raise AssertionError("readable packet snapshot followed a symbolic link")
        try:
            require_state_root(temporary_root / "unbound-state")
        except ProtocolError:
            pass
        else:
            raise AssertionError("a production state operation omitted its static root")
        orphan_state = temporary_root / "orphan-state"
        orphan_claim = orphan_state / "agents" / "orphan" / "claim.json"
        orphan_claim.parent.mkdir(parents=True)
        orphan_claim.write_bytes(canonical_json_bytes({"orphan": True}))
        try:
            verify_state(
                orphan_state, test_capability=_SYNTHETIC_TEST_CAPABILITY
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("an orphan uniqueness claim passed empty-state validation")
        forged_root = temporary_root / "forged-static-root"
        forged_root.mkdir()
        forged_sentinel = temporary_root / "candidate-verifier-executed"
        (forged_root / "integrate.py").write_text(
            "from pathlib import Path\n"
            f"Path({str(forged_sentinel)!r}).write_text('executed')\n"
            "def verify_static(root): return {'status': 'STATIC-LOCKED'}\n",
            encoding="utf-8",
        )
        try:
            load_verified_static_bundle(forged_root)
        except ProtocolError:
            pass
        else:
            raise AssertionError("forged static root verifier was trusted")
        if forged_sentinel.exists():
            raise AssertionError("candidate-root verifier code was executed")

        mock_bundle = temporary_root / "mock-production-bundle"
        mock_bundle.mkdir()
        for name in ("protocol.py", "integrate.py", "prepare.py", "word_count.py"):
            shutil.copyfile(RUN / name, mock_bundle / name)
        mock_declaration = (
            mock_bundle / "static" / "integration" / "source-declaration.json"
        )
        mock_declaration.parent.mkdir(parents=True)
        shutil.copyfile(RUN / "static-inputs" / "source-declaration.json", mock_declaration)
        (mock_bundle / "STATIC-LOCK.json").write_bytes(canonical_json_bytes({"mock": True}))
        commitment_path = temporary_root / "external-static-commitment.json"
        expected_commitment = {"mock_external_commitment": True}
        commitment_path.write_bytes(canonical_json_bytes(expected_commitment))
        wrong_commitment_path = temporary_root / "wrong-external-static-commitment.json"
        wrong_commitment_path.write_bytes(
            canonical_json_bytes({"mock_external_commitment": False})
        )
        mock_reviewer_ids = frozenset(
            f"locked-reviewer-{index:04d}" for index in range(1, 12)
        )
        post_verify_reviewer_resolver_calls = 0

        def mock_trusted_integration() -> dict[str, Any]:
            def mock_verify_static_with_reviewer_ids(
                root: Path,
                *,
                expected_bundle_kind: str,
                expected_external_commitment: Any,
            ) -> tuple[dict[str, Any], frozenset[str]]:
                if (
                    root != mock_bundle
                    or expected_bundle_kind != "PRODUCTION"
                    or expected_external_commitment != expected_commitment
                ):
                    raise ProtocolError("mock external commitment mismatch")
                return (
                    {"schema_version": 2, "status": "STATIC-LOCKED"},
                    mock_reviewer_ids,
                )

            def forbidden_post_verify_reviewer_resolver(*_args: Any) -> frozenset[str]:
                nonlocal post_verify_reviewer_resolver_calls
                post_verify_reviewer_resolver_calls += 1
                raise AssertionError(
                    "protocol reopened reviewer receipts after static verification"
                )

            return {
                "verify_static_with_reviewer_ids": (
                    mock_verify_static_with_reviewer_ids
                ),
                "locked_reviewer_actor_ids": forbidden_post_verify_reviewer_resolver,
            }

        saved_trusted_integration = globals()["trusted_integration_module"]
        globals()["trusted_integration_module"] = mock_trusted_integration
        try:
            loaded_root, _mock_lock, loaded_reviewer_ids = load_verified_static_bundle(
                mock_bundle, commitment_path
            )
            assert loaded_root == mock_bundle
            assert loaded_reviewer_ids == mock_reviewer_ids
            if post_verify_reviewer_resolver_calls != 0:
                raise AssertionError(
                    "protocol used a second reviewer-ID resolver after verification"
                )
            assert require_state_root(
                mock_bundle / "runtime" / "state",
                static_root=mock_bundle,
                external_commitment_path=commitment_path,
            ) == mock_bundle / "runtime" / "state"
            assert require_production_runtime_actor(
                "runtime-agent-0001",
                "mock production actor",
                mock_reviewer_ids,
            ) == "runtime-agent-0001"
            try:
                require_production_runtime_actor(
                    next(iter(mock_reviewer_ids)),
                    "mock production actor",
                    mock_reviewer_ids,
                )
            except ProtocolError:
                pass
            else:
                raise AssertionError("trusted reviewer resolver did not exclude its actor")
            for bad_commitment in (None, wrong_commitment_path):
                try:
                    load_verified_static_bundle(mock_bundle, bad_commitment)
                except ProtocolError:
                    pass
                else:
                    raise AssertionError(
                        "missing or incorrect external commitment was accepted"
                    )
            inside_commitment = mock_bundle / "external-static-commitment.json"
            inside_commitment.write_bytes(canonical_json_bytes(expected_commitment))
            try:
                load_verified_static_bundle(mock_bundle, inside_commitment)
            except ProtocolError:
                pass
            else:
                raise AssertionError("candidate-custodied external commitment was accepted")
        finally:
            globals()["trusted_integration_module"] = saved_trusted_integration

        candidate_protocol_root = temporary_root / "candidate-protocol"
        candidate_protocol_root.mkdir()
        shutil.copyfile(RUN / "protocol.py", candidate_protocol_root / "protocol.py")
        (candidate_protocol_root / "STATIC-LOCK.json").write_bytes(
            canonical_json_bytes({"candidate": True})
        )
        candidate_protocol = runpy.run_path(
            str(candidate_protocol_root / "protocol.py"),
            run_name="v5_candidate_protocol_self_test",
        )
        try:
            candidate_protocol["load_verified_static_bundle"](
                mock_bundle, commitment_path
            )
        except Exception:
            pass
        else:
            raise AssertionError("a candidate-bundle protocol acted as its own trust anchor")

        report_source = temporary_root / "report-static-source"
        (report_source / "static" / "materialized" / "target").mkdir(parents=True)
        (report_source / "static" / "materialized" / "target" / "REQUEST.md").write_text(
            "Synthetic report request.\n", encoding="utf-8"
        )
        (report_source / "static" / "materialized" / "package").mkdir(parents=True)
        (report_source / "static" / "materialized" / "package" / "SKILL.md").write_text(
            "# Synthetic skill\n", encoding="utf-8"
        )
        (report_source / "static" / "materialized" / "common" / "docs").mkdir(
            parents=True
        )
        authority_source = (
            report_source
            / "static"
            / "materialized"
            / "common"
            / "docs"
            / "rust-documentation.json"
        )
        authority_source.write_text('{"authority":"synthetic"}\n', encoding="utf-8")
        (report_source / "schemas").mkdir()
        schema_source = report_source / "schemas" / "attempt-envelope.schema.json"
        schema_source.write_text('{"type":"object"}\n', encoding="utf-8")
        trusted_prepare = run_trusted_module(
            "prepare.py", "v5_report_materialization_self_test"
        )
        tree_digest = trusted_prepare["byte_tree_v1"]
        target_source = report_source / "static" / "materialized" / "target"
        package_source = report_source / "static" / "materialized" / "package"
        report_workspace = temporary_root / "report-workspace"
        report_workspace.mkdir()
        report_launch = {
            "schema_version": 1,
            "status": "READY",
            "role": "report",
            "assignment_id": "r001",
            "slot_id": "r001",
            "run_id": "r001",
            "cell_id": "1" * 32,
            "mode": "E",
            "fixture_id": "synthetic_e",
            "task_mode": "synthetic_test",
            "prompt_regime": "controlled",
            "condition_role": "v5",
            "condition_label": "c0",
            "target_label": "m0",
            "replicate": 1,
            "workspace_root": str(report_workspace),
            "input_root": str(report_workspace / "input"),
            "output_root": str(report_workspace / "output"),
            "target_path": "target/REQUEST.md",
            "output_path": "report.md",
            "schema_paths": [],
            "schedule_sha256": "1" * 64,
            "prompt_sha256": "2" * 64,
            "package_byte_tree_sha256": tree_digest(package_source),
            "target_byte_tree_sha256": tree_digest(target_source),
            "authority_packet_path": "docs/rust-documentation.json",
            "authority_packet_sha256": sha256(authority_source.read_bytes()),
            "authority_packet_visibility": "AGENT_VISIBLE_NEUTRAL",
            "execution_manifest_sha256": "3" * 64,
            "input_packet_sha256": "4" * 64,
            "envelope_spec_sha256": "5" * 64,
        }
        report_entries = sorted(
            [
                {
                    "destination": "input/target",
                    "kind": "BYTE_TREE_V1_DIRECTORY",
                    "source_path": "static/materialized/target",
                    "sha256": report_launch["target_byte_tree_sha256"],
                },
                {
                    "destination": "input/package",
                    "kind": "BYTE_TREE_V1_DIRECTORY",
                    "source_path": "static/materialized/package",
                    "sha256": report_launch["package_byte_tree_sha256"],
                },
                {
                    "destination": "input/docs/rust-documentation.json",
                    "kind": "FILE",
                    "source_path": "static/materialized/common/docs/rust-documentation.json",
                    "sha256": report_launch["authority_packet_sha256"],
                },
            ],
            key=lambda item: item["destination"],
        )
        report_plan = validate_report_input_plan(
            {
                "schema_version": 1,
                "status": "READY",
                "run_id": "r001",
                "cell_id": report_launch["cell_id"],
                "input_alias": "input",
                "output_alias": "output",
                "entries": report_entries,
            },
            report_launch,
        )
        missing_plan_entry = copy.deepcopy(report_plan)
        missing_plan_entry["entries"] = missing_plan_entry["entries"][:-1]
        try:
            validate_report_input_plan(missing_plan_entry, report_launch)
        except ProtocolError:
            pass
        else:
            raise AssertionError("report input plan omitted a required input")
        empty_input = temporary_root / "empty-report-workspace" / "input"
        empty_input.mkdir(parents=True)
        try:
            materialize_report_input_tree(
                empty_input, report_source, report_plan, tree_digest
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("empty report input root was accepted")
        materialize_report_input_tree(
            report_workspace / "input", report_source, report_plan, tree_digest
        )
        verify_report_input_tree(
            report_workspace / "input", report_source, report_plan, tree_digest
        )
        substituted_input = temporary_root / "substituted-report-input"
        shutil.copytree(report_workspace / "input", substituted_input)
        os.chmod(substituted_input, 0o700)
        os.chmod(substituted_input / "docs", 0o700)
        os.chmod(substituted_input / "docs" / "rust-documentation.json", 0o600)
        (substituted_input / "docs" / "rust-documentation.json").write_text(
            "substituted\n", encoding="utf-8"
        )
        try:
            verify_report_input_tree(
                substituted_input, report_source, report_plan, tree_digest
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("substituted report input was accepted")

        inventory_spec = {
            "schema_version": 1,
            "status": "READY",
            "files": [
                {
                    "path": "report.md",
                    "required": True,
                    "max_bytes": 4096,
                    "utf8": True,
                }
            ],
            "final_response": {
                "required": True,
                "max_bytes": 64,
                "utf8": True,
                "utf8_fullmatch_regex": "^report\\.md\\n?$",
            },
            "max_total_output_bytes": 8192,
            "allowed_process_dispositions": ["returned"],
        }
        inventory_spec_bytes = canonical_json_bytes(inventory_spec)
        inventory_plan_bytes = canonical_json_bytes(report_plan)
        inventory_launch = {
            **report_launch,
            "envelope_spec_sha256": sha256(inventory_spec_bytes),
            "input_packet_sha256": sha256(inventory_plan_bytes),
        }
        inventory_launch_bytes = canonical_json_bytes(inventory_launch)
        inventory_agent = "report-agent-00000001"
        inventory_attempt = "r001-attempt-00000001"
        inventory_lease = {
            "schema_version": 1,
            "status": "STARTED",
            "slot_id": "r001",
            "attempt_id": inventory_attempt,
            "agent_id": inventory_agent,
            "lease_token": "a" * 64,
            "launch_record_sha256": sha256(inventory_launch_bytes),
            "launch_record_bytes_base64": base64.b64encode(
                inventory_launch_bytes
            ).decode("ascii"),
            "attempt_root": inventory_launch["output_root"],
            "attempt_root_claim_sha256": sha256(
                inventory_launch["output_root"].encode("utf-8")
            ),
            "envelope_spec_sha256": sha256(inventory_spec_bytes),
            "envelope_spec_bytes_base64": base64.b64encode(
                inventory_spec_bytes
            ).decode("ascii"),
            "input_packet_sha256": sha256(inventory_plan_bytes),
            "input_packet_bytes_base64": base64.b64encode(
                inventory_plan_bytes
            ).decode("ascii"),
        }
        derived_inventory = derive_report_secret_inventory(
            report_source,
            inventory_launch,
            inventory_lease,
            {
                "invocation_blocks": {
                    "v5": "Use the confidential candidate package instructions.",
                    "v4": "",
                    "no_skill": "",
                }
            },
            {
                "packages": {
                    "v5": {
                        "byte_tree_sha256": tree_digest(package_source),
                        "skill_sha256": "b" * 64,
                        "source_path": "static/materialized/package",
                    },
                    "v4": None,
                    "no_skill": None,
                }
            },
            {"source_path": "static/materialized/target"},
        )
        projected_inventory_report, _scorer_projection, _audit_projection = (
            project_report_for_scorer(
                "A",
                (
                    f"Agent {inventory_agent}; cell {inventory_launch['cell_id']}; "
                    f"attempt {inventory_attempt}."
                ).encode("utf-8"),
                derived_inventory,
            )
        )
        if any(
            value.encode("utf-8") in projected_inventory_report
            for value in (
                inventory_agent,
                inventory_launch["cell_id"],
                inventory_attempt,
            )
        ):
            raise AssertionError("derived report-secret inventory omitted a bound runtime ID")

        evaluator_root = temporary_root / "evaluator-static-root"
        evaluator_prompts = evaluator_root / "prompts"
        evaluator_prompts.mkdir(parents=True)
        for role in (
            "scorer",
            "consistency",
            "adjudicator",
            "materiality-reviewer",
            "materiality-adjudicator",
        ):
            shutil.copyfile(
                RUN / "prompts" / f"{role}.md",
                evaluator_prompts / f"{role}.md",
            )
        evaluator_schema = evaluator_root / "schemas" / "score.schema.json"
        evaluator_schema.parent.mkdir()
        shutil.copyfile(RUN / "schemas" / "score.schema.json", evaluator_schema)
        evaluator_documents = {
            "scoring-schedule.json": {
                "claims": [
                    f"{mode}-{reviewer}"
                    for mode in MODES
                    for reviewer in SCORERS
                ]
            },
            "consistency-schedule.json": {
                "claims": [
                    f"{mode}-{reviewer}"
                    for mode in MODES
                    for reviewer in CONSISTENCY_REVIEWERS
                ]
            },
            "report-launch-records": [
                {
                    "workspace_root": str(
                        temporary_root / "evaluator-workspaces" / f"r{index:03d}"
                    )
                }
                for index in range(1, 121)
            ],
        }
        role_digests = {
            role: sha256(f"execution:{role}".encode("utf-8"))
            for role in SEMANTIC_AGENT_ROLES
            if role != "report"
        }
        spec_digests = {
            role: sha256(f"spec:{role}".encode("utf-8"))
            for role in SEMANTIC_AGENT_ROLES
            if role != "report"
        }
        evaluator_contract, _evaluator_prompts = trusted_integration_module()[
            "derive_evaluator_material"
        ](evaluator_root, evaluator_documents, role_digests, spec_digests)
        evaluator_contract_path = (
            evaluator_root
            / "static"
            / "generated"
            / "evaluator-launch-contracts.json"
        )
        evaluator_contract_path.parent.mkdir(parents=True)
        evaluator_contract_path.write_bytes(canonical_json_bytes(evaluator_contract))
        evaluator_documents["evaluator-launch-contracts"] = evaluator_contract
        scorer_packet_bytes = canonical_json_bytes(score_input_first)
        evaluator_launch, evaluator_row = build_expected_evaluator_launch(
            evaluator_root, evaluator_documents, "E-s1", scorer_packet_bytes
        )
        evaluator_workspace = Path(evaluator_launch["workspace_root"])
        evaluator_workspace.mkdir(parents=True)
        materialize_evaluator_input_tree(
            Path(evaluator_launch["input_root"]),
            evaluator_root,
            evaluator_row,
            scorer_packet_bytes,
        )
        verify_evaluator_input_tree(
            Path(evaluator_launch["input_root"]),
            evaluator_root,
            evaluator_row,
            scorer_packet_bytes,
        )
        try:
            build_expected_evaluator_launch(
                evaluator_root,
                evaluator_documents,
                "E-s1",
                pretty_json(score_input_first).encode("utf-8"),
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("noncanonical evaluator input packet bytes were accepted")
        evaluator_input = Path(evaluator_launch["input_root"])
        os.chmod(evaluator_input, 0o700)
        (evaluator_input / "undeclared.txt").write_text("secret\n", encoding="utf-8")
        try:
            verify_evaluator_input_tree(
                evaluator_input,
                evaluator_root,
                evaluator_row,
                scorer_packet_bytes,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("undeclared evaluator input file was accepted")
        receipt_bundle = temporary_root / "bound-receipt-bundle"
        receipt_root = (
            receipt_bundle
            / "runtime"
            / "state"
            / "aggregation"
            / "integration-receipts"
        )
        receipt_root.mkdir(parents=True)
        aggregate_path = receipt_root.parent / "aggregate-context.json"
        aggregate_path.write_bytes(canonical_json_bytes(aggregate))
        receipt_digests: dict[str, str] = {}

        def synthetic_runtime_receipt(
            hook_id: str,
            inputs: dict[str, str],
            outputs: dict[str, str],
        ) -> dict[str, Any]:
            """Build a temp-only runtime-validator fixture.

            ``PASS`` is the runtime schema's validation outcome. This object
            is never an independent-review receipt, never enters a static
            bundle, and cannot authorize either production review boundary.
            """
            phase = INTEGRATION_HOOK_PHASES[hook_id]
            return {
                "schema_version": 2,
                "status": "PASS",
                "phase": phase,
                "hook_id": hook_id,
                "receipt_kind": (
                    "RUNTIME_VALIDATION"
                    if phase == "RUNTIME_COLLECTION"
                    else "POSTRUN_VALIDATION"
                ),
                "actor": {
                    "identity": "synthetic-test-integrator",
                    "role": "SYNTHETIC_TEST_ORCHESTRATOR",
                    "implementation": "protocol.self_test",
                    "version": "v5",
                },
                "input_digests": inputs,
                "output_digests": outputs,
                "result": {
                    "summary": "Synthetic receipt used only by the protocol self-test.",
                    "checks": [
                        {
                            "id": "SYNTHETIC-CHECK",
                            "status": "PASS",
                            "evidence": "The self-test constructed and checked this exact receipt binding.",
                        }
                    ],
                },
            }

        for hook_id in PRE_BIND_RECEIPT_HOOK_IDS:
            common_inputs = {
                **aggregate["input_digests"],
                "static_lock_sha256": aggregate["static_lock_sha256"],
                "rules_sha256": aggregate["rules_sha256"],
            }
            if hook_id == "H-DERIVE-AGGREGATE-CONTEXT":
                inputs = common_inputs
                outputs = {
                    "aggregate_context_sha256": sha256(aggregate_path.read_bytes())
                }
            else:
                inputs = common_inputs
                outputs = {
                    "H-ENFORCE-WORD-COUNTER": {
                        "validated_word_counts_sha256": aggregate["input_digests"]["word_counts_sha256"]
                    },
                    "H-BUILD-VALIDATE-SCORER-REPORT-PROJECTIONS": {
                        "validated_projection_audit_manifest_sha256": aggregate["input_digests"]["projection_audit_manifest_sha256"]
                    },
                    "H-VALIDATE-SCHEDULE-LEASE-ATTEMPT-LEDGER": {
                        "validated_schedule_slots_sha256": aggregate["input_digests"]["schedule_slots_sha256"],
                        "validated_envelopes_sha256": aggregate["input_digests"]["envelopes_sha256"],
                    },
                    "H-SEMANTICALLY-REVALIDATE-ENVELOPES": {
                        "validated_envelopes_sha256": aggregate["input_digests"]["envelopes_sha256"]
                    },
                    "H-VALIDATE-EVALUATOR-INDEPENDENCE-QUALIFICATION": {
                        "validated_scoring_bundle_manifest_sha256": aggregate["input_digests"]["scoring_bundle_manifest_sha256"]
                    },
                    "H-RUN-VALIDATE-MATERIALITY-REVIEWS": {
                        "validated_materiality_ledger_sha256": aggregate["input_digests"]["materiality_ledger_sha256"]
                    },
                }[hook_id]
            receipt = synthetic_runtime_receipt(hook_id, inputs, outputs)
            path = receipt_root / f"{hook_id}.json"
            path.write_bytes(canonical_json_bytes(receipt))
            receipt_digests[hook_id] = sha256(path.read_bytes())
            os.chmod(path, 0o400)
        bind_inputs = {
            "static_lock_sha256": aggregate["static_lock_sha256"],
            "rules_sha256": aggregate["rules_sha256"],
            "aggregate_context_sha256": sha256(aggregate_path.read_bytes()),
            **{
                f"receipt::{hook_id}": receipt_digests[hook_id]
                for hook_id in PRE_BIND_RECEIPT_HOOK_IDS
            },
        }
        bind = synthetic_runtime_receipt(
            "H-BIND-CONTEXT-INPUT-DIGESTS",
            bind_inputs,
            {
                "bound_gate_context_sha256": sha256(canonical_json_bytes(bind_inputs))
            },
        )
        bind_path = receipt_root / "H-BIND-CONTEXT-INPUT-DIGESTS.json"
        bind_path.write_bytes(canonical_json_bytes(bind))
        os.chmod(bind_path, 0o400)
        os.chmod(aggregate_path, 0o400)
        os.chmod(receipt_root, 0o500)
        validate_bound_aggregate_receipts(receipt_bundle, aggregate)
        os.chmod(receipt_root, 0o700)
        os.chmod(bind_path, 0o600)
        bad_bind = copy.deepcopy(bind)
        bad_bind["output_digests"]["bound_gate_context_sha256"] = "0" * 64
        bind_path.write_bytes(canonical_json_bytes(bad_bind))
        os.chmod(bind_path, 0o400)
        os.chmod(receipt_root, 0o500)
        try:
            validate_bound_aggregate_receipts(receipt_bundle, aggregate)
        except ProtocolError:
            pass
        else:
            raise AssertionError("tampered aggregate binding receipt was accepted")
        os.chmod(receipt_root, 0o700)
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
        input_packet_path = temporary_root / "report-input.json"
        input_packet_path.write_bytes(canonical_json_bytes({"synthetic": "report-input"}))
        def synthetic_lease(
            slot_id: str,
            agent_id: str,
            attempt_root: Path,
            *,
            lease_state: Path = state,
            fault_after: str | None = None,
        ) -> dict[str, Any]:
            workspace_root = attempt_root.parent
            input_root = workspace_root / "input"
            input_root.mkdir(parents=True, exist_ok=True)
            role, assignment = {
                "slot-one": ("scorer", "E-s1"),
                "slot-invalid": ("scorer", "E-s2"),
                "slot-format": ("consistency", "E-c1"),
                "slot-race": ("consistency", "E-c2"),
                "slot-recovery": ("adjudicator", "E-a1"),
            }[slot_id]
            launch = {
                "schema_version": 1,
                "status": "READY",
                "role": role,
                "assignment_id": assignment,
                "slot_id": slot_id,
                "run_id": None,
                "cell_id": sha256(slot_id.encode("utf-8"))[:32],
                "mode": "E",
                "fixture_id": None,
                "task_mode": None,
                "prompt_regime": None,
                "condition_role": None,
                "condition_label": None,
                "target_label": None,
                "replicate": None,
                "workspace_root": str(workspace_root),
                "input_root": str(input_root),
                "output_root": str(attempt_root),
                "target_path": None,
                "output_path": "report.md",
                "schema_paths": ["schemas/report.schema.json"],
                "schedule_sha256": "1" * 64,
                "prompt_sha256": "2" * 64,
                "package_byte_tree_sha256": None,
                "target_byte_tree_sha256": None,
                "authority_packet_path": None,
                "authority_packet_sha256": None,
                "authority_packet_visibility": None,
                "execution_manifest_sha256": "6" * 64,
                "input_packet_sha256": sha256(input_packet_path.read_bytes()),
                "envelope_spec_sha256": sha256(spec_path.read_bytes()),
            }
            launch_path = temporary_root / f"{slot_id}-{agent_id}.launch.json"
            launch_path.write_bytes(canonical_json_bytes(launch))
            return acquire_lease(
                lease_state,
                launch_path,
                agent_id,
                spec_path,
                attempt_root,
                input_packet_path,
                fault_after=fault_after,
                test_capability=_SYNTHETIC_TEST_CAPABILITY,
            )

        def synthetic_seal(*args: Any, **kwargs: Any) -> dict[str, Any]:
            return seal_attempt(
                *args,
                **kwargs,
                test_capability=_SYNTHETIC_TEST_CAPABILITY,
            )

        def synthetic_verify(path: Path) -> dict[str, Any]:
            return verify_state(path, test_capability=_SYNTHETIC_TEST_CAPABILITY)

        # Exercise the complete production acquisition branch behind explicit
        # authenticated-boundary seams. This is deliberately more than a unit
        # call to the actor helper: recurrence of an undefined helper name in
        # acquire_lease would fail here.
        production_mock_root = temporary_root / "production-acquire-static"
        (production_mock_root / "runtime").mkdir(parents=True)
        production_spec_path = production_mock_root / "spec.json"
        production_spec_path.write_bytes(spec_path.read_bytes())
        production_workspace = temporary_root / "production-acquire-workspace"
        production_input = production_workspace / "input"
        production_output = production_workspace / "output"
        production_input.mkdir(parents=True)
        production_launch = {
            "schema_version": 1,
            "status": "READY",
            "role": "scorer",
            "assignment_id": "E-s1",
            "slot_id": "production-slot",
            "run_id": None,
            "cell_id": sha256(b"production-slot")[:32],
            "mode": "E",
            "fixture_id": None,
            "task_mode": None,
            "prompt_regime": None,
            "condition_role": None,
            "condition_label": None,
            "target_label": None,
            "replicate": None,
            "workspace_root": str(production_workspace),
            "input_root": str(production_input),
            "output_root": str(production_output),
            "target_path": None,
            "output_path": "report.md",
            "schema_paths": ["schemas/report.schema.json"],
            "schedule_sha256": "1" * 64,
            "prompt_sha256": "2" * 64,
            "package_byte_tree_sha256": None,
            "target_byte_tree_sha256": None,
            "authority_packet_path": None,
            "authority_packet_sha256": None,
            "authority_packet_visibility": None,
            "execution_manifest_sha256": "6" * 64,
            "input_packet_sha256": sha256(input_packet_path.read_bytes()),
            "envelope_spec_sha256": sha256(production_spec_path.read_bytes()),
        }
        production_launch_path = temporary_root / "production-acquire.launch.json"
        production_launch_path.write_bytes(canonical_json_bytes(production_launch))
        production_reviewer_ids = frozenset(
            {"reviewer-actor-0001"}
            | {f"reviewer-actor-{index:04d}" for index in range(2, 12)}
        )
        production_seams = {
            "load_verified_static_bundle": globals()["load_verified_static_bundle"],
            "load_ready_generated_documents": globals()["load_ready_generated_documents"],
            "build_expected_evaluator_launch": globals()["build_expected_evaluator_launch"],
            "materialize_evaluator_input_tree": globals()["materialize_evaluator_input_tree"],
        }
        active_production_launch = [production_launch]
        forbid_production_materialization = [False]
        globals()["load_verified_static_bundle"] = (
            lambda static_root, external_commitment_path=None: (
                Path(static_root).resolve(),
                {"status": "STATIC-LOCKED"},
                production_reviewer_ids,
            )
        )
        globals()["load_ready_generated_documents"] = lambda _root: {}
        globals()["build_expected_evaluator_launch"] = (
            lambda _root, _documents, _assignment, _packet: (
                active_production_launch[0],
                {"envelope_spec_path": "spec.json"},
            )
        )
        def mock_production_materialization(*_args: Any) -> None:
            if forbid_production_materialization[0]:
                raise AssertionError(
                    "poisoned peer was detected only after input materialization"
                )

        globals()["materialize_evaluator_input_tree"] = mock_production_materialization
        try:
            production_lease = acquire_lease(
                production_mock_root / "runtime" / "state",
                production_launch_path,
                "runtime-agent-9999",
                production_spec_path,
                production_output,
                input_packet_path,
                static_root=production_mock_root,
                external_commitment_path=commitment_path,
            )
            if production_lease["agent_id"] != "runtime-agent-9999":
                raise AssertionError("production acquisition changed its actor identity")

            def make_production_launch(
                slot_id: str, assignment_id: str
            ) -> tuple[dict[str, Any], Path, Path]:
                workspace = temporary_root / f"{slot_id}-workspace"
                input_root = workspace / "input"
                output_root = workspace / "output"
                input_root.mkdir(parents=True)
                launch = dict(production_launch)
                launch.update(
                    {
                        "assignment_id": assignment_id,
                        "slot_id": slot_id,
                        "cell_id": sha256(slot_id.encode("utf-8"))[:32],
                        "mode": assignment_id.split("-", 1)[0],
                        "workspace_root": str(workspace),
                        "input_root": str(input_root),
                        "output_root": str(output_root),
                    }
                )
                launch_path = temporary_root / f"{slot_id}.launch.json"
                launch_path.write_bytes(canonical_json_bytes(launch))
                return launch, launch_path, output_root

            second_launch, second_launch_path, second_output = make_production_launch(
                "production-slot-two", "F-s1"
            )
            active_production_launch[0] = second_launch
            second_lease = acquire_lease(
                production_mock_root / "runtime" / "state",
                second_launch_path,
                "runtime-agent-9998",
                production_spec_path,
                second_output,
                input_packet_path,
                static_root=production_mock_root,
                external_commitment_path=commitment_path,
            )
            if second_lease["agent_id"] != "runtime-agent-9998":
                raise AssertionError("second production acquisition changed its actor identity")
            try:
                active_production_launch[0] = production_launch
                acquire_lease(
                    production_mock_root / "runtime" / "state",
                    production_launch_path,
                    "reviewer-actor-0001",
                    production_spec_path,
                    production_output,
                    input_packet_path,
                    static_root=production_mock_root,
                    external_commitment_path=commitment_path,
                )
            except ProtocolError:
                pass
            else:
                raise AssertionError("production acquisition reused a locked reviewer")

            def poison_peer_lease(root: Path, poisoned_actor: str) -> None:
                peer_path = root / "runtime/state/slots/production-slot/lease.json"
                peer = read_json(peer_path)
                peer["agent_id"] = poisoned_actor
                os.chmod(peer_path, 0o600)
                peer_path.write_bytes(canonical_json_bytes(peer))
                os.chmod(peer_path, 0o400)

            def require_poison_reason(error: ProtocolError, poisoned_actor: str) -> None:
                expected_reason = (
                    "permanently ineligible"
                    if poisoned_actor == "reviewer-actor-0001"
                    else "canonical 16-128 byte"
                )
                if expected_reason not in str(error):
                    raise AssertionError(
                        "persisted peer-lease rejection had the wrong reason"
                    ) from error

            # Every production mutation validates all authoritative peer leases
            # under the same operation lock. A poisoned, otherwise valid peer must
            # stop both acquisition and sealing before either target is changed.
            for poison_index, poisoned_actor in enumerate(
                ("reviewer-actor-0001", "invalid-alias"), start=1
            ):
                poisoned_acquire_root = (
                    temporary_root / f"poisoned-acquire-static-{poison_index}"
                )
                (poisoned_acquire_root / "runtime").mkdir(parents=True)
                shutil.copytree(
                    production_mock_root / "runtime/state",
                    poisoned_acquire_root / "runtime/state",
                )
                (poisoned_acquire_root / "spec.json").write_bytes(
                    production_spec_path.read_bytes()
                )
                poison_peer_lease(poisoned_acquire_root, poisoned_actor)
                target_launch, target_launch_path, target_output = make_production_launch(
                    f"poison-acquire-target-{poison_index}", "V-s1"
                )
                active_production_launch[0] = target_launch
                forbid_production_materialization[0] = True
                try:
                    acquire_lease(
                        poisoned_acquire_root / "runtime/state",
                        target_launch_path,
                        f"runtime-agent-88{poison_index:02d}",
                        poisoned_acquire_root / "spec.json",
                        target_output,
                        input_packet_path,
                        static_root=poisoned_acquire_root,
                        external_commitment_path=commitment_path,
                    )
                except ProtocolError as error:
                    require_poison_reason(error, poisoned_actor)
                else:
                    raise AssertionError("production acquisition accepted a poisoned peer lease")
                finally:
                    forbid_production_materialization[0] = False
                if (
                    (poisoned_acquire_root / "runtime/state/slots" / target_launch["slot_id"]).exists()
                    or target_output.exists()
                ):
                    raise AssertionError(
                        "production acquisition mutated state after finding a poisoned peer lease"
                    )

                poisoned_seal_root = (
                    temporary_root / f"poisoned-seal-static-{poison_index}"
                )
                (poisoned_seal_root / "runtime").mkdir(parents=True)
                shutil.copytree(
                    production_mock_root / "runtime/state",
                    poisoned_seal_root / "runtime/state",
                )
                (poisoned_seal_root / "spec.json").write_bytes(
                    production_spec_path.read_bytes()
                )
                poison_peer_lease(poisoned_seal_root, poisoned_actor)
                second_slot = poisoned_seal_root / "runtime/state/slots/production-slot-two"
                try:
                    seal_attempt(
                        poisoned_seal_root / "runtime/state",
                        second_lease["slot_id"],
                        second_lease["lease_token"],
                        second_lease["agent_id"],
                        second_output,
                        None,
                        "PROCESS-EXITED",
                        0,
                        {},
                        static_root=poisoned_seal_root,
                        external_commitment_path=commitment_path,
                    )
                except ProtocolError as error:
                    require_poison_reason(error, poisoned_actor)
                else:
                    raise AssertionError("production sealing accepted a poisoned peer lease")
                if any(
                    (second_slot / name).exists()
                    for name in (
                        "terminal-claim.json",
                        "canonical.json",
                        "seal-failure.json",
                    )
                ):
                    raise AssertionError(
                        "production sealing mutated state after finding a poisoned peer lease"
                    )
        finally:
            for name, value in production_seams.items():
                globals()[name] = value

        for fault_point in (
            "lease-cas",
            "attempt-root",
            "agent-claim",
            "root-claim",
            "ready",
        ):
            fault_state = temporary_root / f"fault-state-{fault_point}"
            fault_output = temporary_root / f"fault-workspace-{fault_point}" / "output"
            try:
                synthetic_lease(
                    "slot-one",
                    "fault-agent",
                    fault_output,
                    lease_state=fault_state,
                    fault_after=fault_point,
                )
            except InjectedFault:
                pass
            else:
                raise AssertionError(f"lease fault injection did not fire: {fault_point}")
            recovered_lease = synthetic_lease(
                "slot-one",
                "fault-agent",
                fault_output,
                lease_state=fault_state,
            )
            ready_path = fault_state / "slots" / "slot-one" / "lease-ready.json"
            assert ready_path.is_file()
            assert validate_lease(recovered_lease)["agent_id"] == "fault-agent"

        output = temporary_root / "workspace-one" / "output"
        lease = synthetic_lease("slot-one", "agent-one", output)
        try:
            synthetic_lease(
                "slot-one",
                "agent-two",
                temporary_root / "workspace-one-duplicate" / "output",
            )
        except LeaseAlreadyExists:
            pass
        else:
            raise AssertionError("second started-attempt lease was accepted")
        (output / "report.md").write_text("synthetic report\n", encoding="utf-8")
        pointer = synthetic_seal(
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
        for forged_actor, expected_fragment in (
            ("reviewer-actor-0001", "permanently ineligible"),
            ("invalid-alias", "canonical 16-128 byte"),
        ):
            forged_state = temporary_root / f"persisted-{forged_actor}-state"
            shutil.copytree(state, forged_state)
            forged_lease_path = forged_state / "slots" / "slot-one" / "lease.json"
            os.chmod(forged_lease_path, 0o600)
            forged_lease = read_json(forged_lease_path)
            forged_lease["agent_id"] = forged_actor
            forged_lease_path.write_bytes(canonical_json_bytes(forged_lease))
            os.chmod(forged_lease_path, 0o400)
            try:
                with operation_lock(forged_state):
                    _verify_state_locked(
                        forged_state,
                        production_reviewer_ids=frozenset(
                            {"reviewer-actor-0001"}
                        ),
                    )
            except ProtocolError as error:
                if expected_fragment not in str(error):
                    raise AssertionError(
                        "persisted production actor failed for the wrong reason"
                    ) from error
            else:
                raise AssertionError(
                    "persisted reviewer/alias actor survived production state verification"
                )
        try:
            synthetic_seal(state, "slot-one", lease["lease_token"], "agent-one", output, b"replacement", "returned", 0, {})
        except CanonicalAlreadySealed:
            pass
        else:
            raise AssertionError("canonical envelope was replaced")

        invalid_output = temporary_root / "workspace-invalid" / "output"
        invalid_lease = synthetic_lease("slot-invalid", "agent-invalid", invalid_output)
        (invalid_output / "extra-empty-directory").mkdir()
        invalid_pointer = synthetic_seal(
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

        format_output = temporary_root / "workspace-format" / "output"
        format_lease = synthetic_lease("slot-format", "agent-format", format_output)
        (format_output / "report.md").write_text("format report\n", encoding="utf-8")
        format_pointer = synthetic_seal(
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

        race_output = temporary_root / "workspace-race" / "output"
        race_lease = synthetic_lease("slot-race", "agent-race", race_output)
        (race_output / "report.md").write_text("race report\n", encoding="utf-8")

        def race_seal(marker: str) -> str:
            try:
                synthetic_seal(
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

        recovery_output = temporary_root / "workspace-recovery" / "output"
        recovery_lease = synthetic_lease(
            "slot-recovery", "agent-recovery", recovery_output
        )
        (recovery_output / "report.md").write_text(
            "recovery synthetic report\n", encoding="utf-8"
        )
        try:
            synthetic_seal(
                state,
                "slot-recovery",
                recovery_lease["lease_token"],
                "agent-recovery",
                recovery_output,
                b"report.md\n",
                "returned",
                0,
                {"synthetic": True},
                fault_after="terminal-claim",
            )
        except InjectedFault:
            pass
        else:
            raise AssertionError("terminal-claim fault injection did not fire")
        incomplete = synthetic_verify(state)
        recovery_row = next(
            row for row in incomplete["slots"] if row["slot_id"] == "slot-recovery"
        )
        assert recovery_row["status"] == "TERMINAL_CLAIMED_INCOMPLETE"
        recovery_pointer = synthetic_seal(
            state,
            "slot-recovery",
            recovery_lease["lease_token"],
            "agent-recovery",
            recovery_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        assert recovery_pointer["format_valid"] is True
        assert recovery_pointer["semantic_valid"] is False
        verified = synthetic_verify(state)
        assert len(verified["slots"]) == 5
        assert sum(row["status"] == "SEALED" for row in verified["slots"]) == 5
        assert verified["complete"] is True
        assert verified["state_valid"] is False
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
    derive_aggregate = subcommands.add_parser("derive-aggregate-context")
    derive_aggregate.add_argument("--static-root", type=Path, required=True)
    derive_aggregate.add_argument("--external-commitment", type=Path, required=True)
    bound_gates = subcommands.add_parser("evaluate-bound-gates")
    bound_gates.add_argument("--static-root", type=Path, required=True)
    bound_gates.add_argument("--external-commitment", type=Path, required=True)
    evaluator_launch = subcommands.add_parser("build-evaluator-launch")
    evaluator_launch.add_argument("--static-root", type=Path, required=True)
    evaluator_launch.add_argument("--external-commitment", type=Path, required=True)
    evaluator_launch.add_argument("--assignment", required=True)
    evaluator_launch.add_argument("--input-packet", type=Path, required=True)
    atoms = subcommands.add_parser("validate-atoms")
    atoms.add_argument("manifest", type=Path)
    rules = subcommands.add_parser("validate-rules")
    rules.add_argument("inventory", type=Path)
    score = subcommands.add_parser("validate-score")
    score.add_argument("--score", type=Path, required=True)
    score.add_argument("--atoms", type=Path, required=True)
    score.add_argument("--rules", type=Path, required=True)
    score.add_argument("--input-packet", type=Path, required=True)
    score.add_argument("--scorer", choices=SCORERS, required=True)
    consistency_packet = subcommands.add_parser("build-consistency")
    consistency_packet.add_argument("--score-s1", type=Path, required=True)
    consistency_packet.add_argument("--score-s2", type=Path, required=True)
    consistency_packet.add_argument("--input-s1", type=Path, required=True)
    consistency_packet.add_argument("--input-s2", type=Path, required=True)
    consistency_packet.add_argument("--atoms", type=Path, required=True)
    consistency_packet.add_argument("--rules", type=Path, required=True)
    consistency_packet.add_argument("--evidence", type=Path, required=True)
    consistency = subcommands.add_parser("validate-consistency")
    consistency.add_argument("--consistency", type=Path, required=True)
    consistency.add_argument("--atoms", type=Path, required=True)
    consistency.add_argument("--rules", type=Path, required=True)
    consistency.add_argument("--input-packet", type=Path, required=True)
    consistency.add_argument("--reviewer", choices=CONSISTENCY_REVIEWERS, required=True)
    packet = subcommands.add_parser("build-adjudication")
    packet.add_argument("--score-s1", type=Path, required=True)
    packet.add_argument("--score-s2", type=Path, required=True)
    packet.add_argument("--input-s1", type=Path, required=True)
    packet.add_argument("--input-s2", type=Path, required=True)
    packet.add_argument("--consistency-c1", type=Path, required=True)
    packet.add_argument("--consistency-c2", type=Path, required=True)
    packet.add_argument("--atoms", type=Path, required=True)
    packet.add_argument("--rules", type=Path, required=True)
    packet.add_argument("--evidence", type=Path, required=True)
    adjudication_validate = subcommands.add_parser("validate-adjudication")
    adjudication_validate.add_argument("--adjudication", type=Path, required=True)
    adjudication_validate.add_argument("--input-packet", type=Path, required=True)
    merge = subcommands.add_parser("merge-scores")
    merge.add_argument("--score-s1", type=Path, required=True)
    merge.add_argument("--score-s2", type=Path, required=True)
    merge.add_argument("--input-s1", type=Path, required=True)
    merge.add_argument("--input-s2", type=Path, required=True)
    merge.add_argument("--consistency-c1", type=Path, required=True)
    merge.add_argument("--consistency-c2", type=Path, required=True)
    merge.add_argument("--atoms", type=Path, required=True)
    merge.add_argument("--rules", type=Path, required=True)
    merge.add_argument("--evidence", type=Path, required=True)
    merge.add_argument("--adjudication", type=Path)
    materiality_packet = subcommands.add_parser("build-materiality-review-packet")
    for scope in MATERIALITY_SCOPES:
        materiality_packet.add_argument(
            "--" + scope.lower().replace("_", "-"), type=Path, required=True
        )
    materiality_review = subcommands.add_parser("validate-materiality-review")
    materiality_review.add_argument("--review", type=Path, required=True)
    materiality_review.add_argument("--input-packet", type=Path, required=True)
    materiality_review.add_argument("--reviewer", choices=MATERIALITY_REVIEWERS, required=True)
    materiality_adjudication_packet = subcommands.add_parser(
        "build-materiality-adjudication"
    )
    materiality_adjudication_packet.add_argument("--input-packet", type=Path, required=True)
    materiality_adjudication_packet.add_argument("--review-m1", type=Path, required=True)
    materiality_adjudication_packet.add_argument("--review-m2", type=Path, required=True)
    materiality_adjudication = subcommands.add_parser(
        "validate-materiality-adjudication"
    )
    materiality_adjudication.add_argument("--adjudication", type=Path, required=True)
    materiality_adjudication.add_argument("--input-packet", type=Path, required=True)
    materiality_merge = subcommands.add_parser("merge-materiality")
    materiality_merge.add_argument("--input-packet", type=Path, required=True)
    materiality_merge.add_argument("--review-m1", type=Path, required=True)
    materiality_merge.add_argument("--review-m2", type=Path, required=True)
    materiality_merge.add_argument("--adjudication", type=Path)
    gates = subcommands.add_parser("evaluate-gates")
    gates.add_argument("context", type=Path)
    lease = subcommands.add_parser("lease")
    lease.add_argument("--state-root", type=Path, required=True)
    lease.add_argument("--static-root", type=Path, required=True)
    lease.add_argument("--external-commitment", type=Path, required=True)
    lease.add_argument("--launch", type=Path, required=True)
    lease.add_argument("--agent", required=True)
    lease.add_argument("--envelope-spec", type=Path, required=True)
    lease.add_argument("--attempt-root", type=Path, required=True)
    lease.add_argument("--input-packet", type=Path, required=True)
    seal = subcommands.add_parser("seal-attempt")
    seal.add_argument("--state-root", type=Path, required=True)
    seal.add_argument("--static-root", type=Path, required=True)
    seal.add_argument("--external-commitment", type=Path, required=True)
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
    verify.add_argument("--static-root", type=Path, required=True)
    verify.add_argument("--external-commitment", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "verify-draft":
        verify_draft()
    elif args.command == "self-test":
        verify_draft()
        self_test()
    elif args.command == "derive-aggregate-context":
        sys.stdout.buffer.write(
            canonical_json_bytes(
                derive_aggregate_context(args.static_root, args.external_commitment)
            )
        )
    elif args.command == "evaluate-bound-gates":
        print(
            pretty_json(
                evaluate_bound_gates(args.static_root, args.external_commitment)
            ),
            end="",
        )
    elif args.command == "build-evaluator-launch":
        root, _lock, _reviewer_ids = load_verified_static_bundle(
            args.static_root, args.external_commitment
        )
        documents = load_ready_generated_documents(root)
        launch, _row = build_expected_evaluator_launch(
            root,
            documents,
            args.assignment,
            args.input_packet.read_bytes(),
        )
        sys.stdout.buffer.write(canonical_json_bytes(launch))
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
                    read_json(args.input_packet),
                )
            ),
            end="",
        )
    elif args.command == "build-consistency":
        print(
            pretty_json(
                build_consistency_packet(
                    read_json(args.score_s1),
                    read_json(args.score_s2),
                    read_json(args.input_s1),
                    read_json(args.input_s2),
                    read_json(args.atoms),
                    read_json(args.rules),
                    args.evidence,
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
                    read_json(args.input_packet),
                    args.reviewer,
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
                    read_json(args.input_s1),
                    read_json(args.input_s2),
                    read_json(args.consistency_c1),
                    read_json(args.consistency_c2),
                    read_json(args.atoms),
                    read_json(args.rules),
                    args.evidence,
                )
            ),
            end="",
        )
    elif args.command == "validate-adjudication":
        print(
            pretty_json(
                validate_adjudication(
                    read_json(args.adjudication), read_json(args.input_packet)
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
                    read_json(args.input_s1),
                    read_json(args.input_s2),
                    read_json(args.consistency_c1),
                    read_json(args.consistency_c2),
                    read_json(args.atoms),
                    read_json(args.rules),
                    args.evidence,
                    read_json(args.adjudication) if args.adjudication is not None else None,
                )
            ),
            end="",
        )
    elif args.command == "build-materiality-review-packet":
        print(
            pretty_json(
                build_materiality_review_packet(
                    {
                        scope: getattr(args, scope.lower())
                        for scope in MATERIALITY_SCOPES
                    }
                )
            ),
            end="",
        )
    elif args.command == "validate-materiality-review":
        print(
            pretty_json(
                validate_materiality_review(
                    read_json(args.review), read_json(args.input_packet), args.reviewer
                )
            ),
            end="",
        )
    elif args.command == "build-materiality-adjudication":
        print(
            pretty_json(
                build_materiality_adjudication_packet(
                    read_json(args.input_packet),
                    read_json(args.review_m1),
                    read_json(args.review_m2),
                )
            ),
            end="",
        )
    elif args.command == "validate-materiality-adjudication":
        print(
            pretty_json(
                validate_materiality_adjudication(
                    read_json(args.adjudication), read_json(args.input_packet)
                )
            ),
            end="",
        )
    elif args.command == "merge-materiality":
        print(
            pretty_json(
                merge_materiality_ledger(
                    read_json(args.input_packet),
                    read_json(args.review_m1),
                    read_json(args.review_m2),
                    read_json(args.adjudication) if args.adjudication else None,
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
        print(
            pretty_json(
                acquire_lease(
                    args.state_root,
                    args.launch,
                    args.agent,
                    args.envelope_spec,
                    args.attempt_root,
                    args.input_packet,
                    static_root=args.static_root,
                    external_commitment_path=args.external_commitment,
                )
            ),
            end="",
        )
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
                    static_root=args.static_root,
                    external_commitment_path=args.external_commitment,
                )
            ),
            end="",
        )
    else:
        print(
            pretty_json(
                verify_state(
                    args.state_root,
                    static_root=args.static_root,
                    external_commitment_path=args.external_commitment,
                )
            ),
            end="",
        )


if __name__ == "__main__":
    main()
