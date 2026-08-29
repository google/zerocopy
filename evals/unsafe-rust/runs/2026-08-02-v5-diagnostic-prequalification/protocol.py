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
import binascii
import contextlib
import copy
import ctypes
import errno
import fcntl
import hashlib
import json
import math
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
from typing import Any, Callable, Iterator, NamedTuple


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
AGGREGATE_BUILDER_ID = "v5-diagnostic-aggregate-context-v3"
AGGREGATION_STAGE_MANIFEST_ALGORITHM = "V5_AGGREGATION_STAGE_MANIFEST_V1"
AGGREGATION_TERMINAL_FAILURE_ALGORITHM = "V5_AGGREGATION_TERMINAL_FAILURE_V1"
AGGREGATION_PENDING_STAGE_PREFIX = ".pending-"
AGGREGATION_STAGE_ORDER = (
    "01-report-products",
    "02-scorer-products",
    "03-consistency-products",
    "04-score-products",
    "05-materiality-products",
    "final",
)
PROJECTION_INVENTORY_BUILDER_ID = "v5-report-secret-inventory-v1"
DIAGNOSTIC_CONTRACT_VERSIONS = {
    "DRAFT": "v5-diagnostic-prequalification-draft-1",
    "READY": "v5-diagnostic-prequalification-1",
}
AUTHENTICATED_REVIEW_EVIDENCE_ALGORITHM = "V5_AUTHENTICATED_REVIEW_EVIDENCE_V1"
SOURCE_REVIEW_KINDS = {
    "oracle-review-1.json": "INDEPENDENT_ORACLE",
    "oracle-review-2.json": "INDEPENDENT_ORACLE",
    "coherence-review.json": "COHERENCE",
}
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
SNAPSHOT_REVIEW_HOOK_IDS = tuple(sorted(
    hook_id
    for hook_id in EXPECTED_INTEGRATION_HOOK_IDS
    if INTEGRATION_HOOK_PHASES[hook_id] == "SNAPSHOT_REVIEW"
))
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


class AggregationStageDerivable(ProtocolError):
    """Read-only progress reached a stage that has not yet been published."""

    def __init__(self, progress: dict[str, Any]):
        super().__init__(
            f"aggregation stage is derivable but unpublished: {progress['current_stage']}"
        )
        self.progress = progress


_SYNTHETIC_TEST_CAPABILITY = object()
_PRODUCTION_LEASE_CAPABILITY = object()
AGGREGATION_COORDINATOR_CLAIM = "coordinator-claim.json"
AGGREGATION_TERMINAL_FAILURE = "terminal-failure.json"
ENCODED_OUTPUT_PATH_PREFIX = "_encoded-posix-path/"
MAX_ENVELOPE_CAPTURE_BYTES = 4 * 1024 * 1024
MAX_OUTPUT_CAPTURE_ENTRIES = 4096
MAX_OUTPUT_CAPTURE_PATH_BYTES = 256 * 1024


class OversizedFinalResponse(NamedTuple):
    """Stable source size plus the bounded prefix authenticated at sealing."""

    size: int
    prefix: bytes


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


def reject_json_surrogates(value: Any, label: str) -> None:
    """Iteratively reject strings that are not Unicode scalar sequences."""

    pending = [value]
    seen_containers: set[int] = set()
    while pending:
        item = pending.pop()
        if isinstance(item, str):
            if any(0xD800 <= ord(character) <= 0xDFFF for character in item):
                raise ProtocolError(f"{label} contains an unpaired Unicode surrogate")
        elif isinstance(item, dict):
            identity = id(item)
            if identity in seen_containers:
                continue
            seen_containers.add(identity)
            pending.extend(item.keys())
            pending.extend(item.values())
        elif isinstance(item, (list, tuple)):
            identity = id(item)
            if identity in seen_containers:
                continue
            seen_containers.add(identity)
            pending.extend(item)


def reject_json_nonfinite_numbers(value: Any, label: str) -> None:
    """Iteratively reject exponent-overflow floats produced by json.loads."""

    pending = [value]
    seen_containers: set[int] = set()
    while pending:
        item = pending.pop()
        if isinstance(item, float) and not math.isfinite(item):
            raise ProtocolError(f"{label} contains a non-finite JSON number")
        if isinstance(item, dict):
            identity = id(item)
            if identity in seen_containers:
                continue
            seen_containers.add(identity)
            pending.extend(item.keys())
            pending.extend(item.values())
        elif isinstance(item, (list, tuple)):
            identity = id(item)
            if identity in seen_containers:
                continue
            seen_containers.add(identity)
            pending.extend(item)


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
        value = json.loads(
            text,
            object_pairs_hook=reject_duplicate_json_keys,
            parse_constant=reject_json_constant,
        )
        reject_json_surrogates(value, label)
        reject_json_nonfinite_numbers(value, label)
        return value
    except ProtocolError:
        raise
    except RecursionError as error:
        raise ProtocolError(f"{label} exceeds the JSON nesting limit") from error
    except json.JSONDecodeError as error:
        raise ProtocolError(f"{label} is not valid JSON") from error
    except ValueError as error:
        raise ProtocolError(f"{label} contains an unsupported JSON value") from error


def canonical_json_bytes(value: Any) -> bytes:
    try:
        reject_json_surrogates(value, "canonical JSON value")
        encoded = json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        return (encoded + "\n").encode("utf-8")
    except (TypeError, ValueError, UnicodeEncodeError, RecursionError) as error:
        raise ProtocolError("value is not canonical finite JSON") from error


def pretty_json(value: Any) -> str:
    try:
        reject_json_surrogates(value, "pretty JSON value")
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
    except (TypeError, ValueError, UnicodeEncodeError, RecursionError) as error:
        raise ProtocolError("value is not finite JSON") from error


def read_json(path: Path) -> Any:
    return strict_json_loads(path.read_bytes(), str(path))


def read_bounded_file_prefix_and_size(
    path: Path, max_bytes: int, label: str
) -> tuple[bytes, int]:
    """Read a stable regular-file prefix and bind its actual source size."""

    flags = (
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise ProtocolError(f"{label} is not a readable regular file") from error
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise ProtocolError(f"{label} is not a regular file")
        chunks: list[bytes] = []
        remaining = max_bytes + 1
        while remaining:
            chunk = os.read(descriptor, min(1024 * 1024, remaining))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        after = os.fstat(descriptor)
        if (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        ) != (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        ):
            raise ProtocolError(f"{label} changed during bounded capture")
        data = b"".join(chunks)
        if before.st_size <= max_bytes and len(data) != before.st_size:
            raise ProtocolError(f"{label} was not completely captured")
        if before.st_size > max_bytes and len(data) != max_bytes + 1:
            raise ProtocolError(f"{label} oversize sentinel capture is incomplete")
        return data, before.st_size
    finally:
        os.close(descriptor)


def read_bounded_file_prefix(path: Path, max_bytes: int, label: str) -> bytes:
    """Read a stable regular-file prefix, retaining at most ``max_bytes + 1``."""

    return read_bounded_file_prefix_and_size(path, max_bytes, label)[0]


def read_bounded_final_response(
    path: Path, max_bytes: int, label: str
) -> bytes | OversizedFinalResponse:
    prefix, size = read_bounded_file_prefix_and_size(path, max_bytes, label)
    if size <= max_bytes:
        return prefix
    return OversizedFinalResponse(size=size, prefix=prefix)


def require_exact_keys(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        actual = sorted(value) if isinstance(value, dict) else type(value).__name__
        raise ProtocolError(f"{label} keys mismatch: {actual!r}")
    return value


def require_safe_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or not SAFE_ID.fullmatch(value):
        raise ProtocolError(f"invalid {label}: {value!r}")
    return value


def path_entry_exists(path: Path) -> bool:
    """Return whether a directory entry exists, including a dangling symlink."""

    return path.exists() or path.is_symlink()


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
        or not path.parts
        or path.as_posix() != value
        or "\\" in value
        or value.endswith("/")
        or any(ord(character) < 32 for character in value)
        or any(part in ("", ".", "..") for part in path.parts)
    ):
        raise ProtocolError(f"invalid {label}: {value!r}")
    return value


def encode_output_path_token(value: str) -> str:
    """Represent every POSIX relative pathname as canonical JSON-safe text."""

    if not isinstance(value, str):
        raise ProtocolError("captured output path must be a filesystem string")
    raw = os.fsencode(value)
    try:
        portable = raw.decode("utf-8", errors="strict")
        require_relative_file(portable, "captured output path")
    except (UnicodeDecodeError, ProtocolError):
        portable = None
    if portable is not None and not portable.startswith(ENCODED_OUTPUT_PATH_PREFIX):
        return portable
    encoded = base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=")
    if not encoded:
        raise ProtocolError("captured output path is empty")
    return ENCODED_OUTPUT_PATH_PREFIX + encoded


def decode_output_path_token(value: Any) -> tuple[bytes, bool]:
    """Validate/decode one canonical output token; bool means portable path."""

    if not isinstance(value, str) or not value:
        raise ProtocolError("envelope output path token is invalid")
    if not value.startswith(ENCODED_OUTPUT_PATH_PREFIX):
        portable = require_relative_file(value, "envelope output path")
        return portable.encode("utf-8"), True
    encoded = value.removeprefix(ENCODED_OUTPUT_PATH_PREFIX)
    if not encoded or re.fullmatch(r"[A-Za-z0-9_-]+", encoded) is None:
        raise ProtocolError("encoded envelope output path token is malformed")
    padded = encoded + "=" * ((4 - len(encoded) % 4) % 4)
    try:
        raw = base64.b64decode(padded, altchars=b"-_", validate=True)
    except (ValueError, binascii.Error) as error:
        raise ProtocolError("encoded envelope output path token is malformed") from error
    if base64.urlsafe_b64encode(raw).decode("ascii").rstrip("=") != encoded:
        raise ProtocolError("encoded envelope output path token is noncanonical")
    parts = raw.split(b"/")
    if (
        not raw
        or raw.startswith(b"/")
        or raw.endswith(b"/")
        or b"\x00" in raw
        or any(part in (b"", b".", b"..") for part in parts)
    ):
        raise ProtocolError("encoded envelope output path bytes are not relative")
    try:
        decoded = raw.decode("utf-8", errors="strict")
        require_relative_file(decoded, "decoded envelope output path")
    except (UnicodeDecodeError, ProtocolError):
        decoded = None
    if decoded is not None and not decoded.startswith(ENCODED_OUTPUT_PATH_PREFIX):
        raise ProtocolError("portable envelope output path was unnecessarily encoded")
    return raw, False


def output_capture_limit_path(reason: str) -> str:
    suffix_by_reason = {
        "entry-count": "capture-entry-limit",
        "path-bytes": "capture-path-byte-limit",
    }
    try:
        suffix = suffix_by_reason[reason]
    except KeyError as error:
        raise ProtocolError("output capture-limit reason is invalid") from error
    return encode_output_path_token(ENCODED_OUTPUT_PATH_PREFIX + suffix)


def output_capture_limit_violation(path: Any) -> str:
    for reason in ("entry-count", "path-bytes"):
        if path == output_capture_limit_path(reason):
            return f"capture-limit:{reason}"
    raise ProtocolError("output capture-limit sentinel path is invalid")


def describe_final_response(
    value: bytes | OversizedFinalResponse | None,
) -> tuple[bytes | None, dict[str, Any]]:
    """Normalize a response into retained bytes and an authenticated descriptor."""

    if value is None:
        return None, {
            "present": False,
            "size": None,
            "sha256": None,
            "prefix_sha256": None,
        }
    if type(value) is bytes:
        size = len(value)
        if size <= MAX_ENVELOPE_CAPTURE_BYTES:
            return value, {
                "present": True,
                "size": size,
                "sha256": sha256(value),
                "prefix_sha256": None,
            }
        prefix = value[: MAX_ENVELOPE_CAPTURE_BYTES + 1]
    elif type(value) is OversizedFinalResponse:
        size = value.size
        prefix = value.prefix
        if (
            type(size) is not int
            or size <= MAX_ENVELOPE_CAPTURE_BYTES
            or type(prefix) is not bytes
            or len(prefix) != MAX_ENVELOPE_CAPTURE_BYTES + 1
        ):
            raise ProtocolError("oversized final-response descriptor is invalid")
    else:
        raise ProtocolError(
            "final response must be bytes, a bounded oversized descriptor, or null"
        )
    return None, {
        "present": True,
        "size": size,
        "sha256": None,
        "prefix_sha256": sha256(prefix),
    }


def valid_final_response_binding(
    size: Any, digest: Any, prefix_digest: Any
) -> bool:
    if size is None:
        return digest is None and prefix_digest is None
    if type(size) is not int or size < 0:
        return False
    if size <= MAX_ENVELOPE_CAPTURE_BYTES:
        return (
            isinstance(digest, str)
            and HEX64.fullmatch(digest) is not None
            and prefix_digest is None
        )
    return (
        digest is None
        and isinstance(prefix_digest, str)
        and HEX64.fullmatch(prefix_digest) is not None
    )


def envelope_payload_relative_path(path_token: str) -> PurePosixPath:
    raw, _portable = decode_output_path_token(path_token)
    # Never mirror an agent-controlled pathname beneath the longer private
    # staging prefix: a path valid in the workspace can exceed PATH_MAX there.
    # The envelope record carries the injective pathname token; payload storage
    # is uniformly fixed-width and content-addressed by the raw path bytes.
    return PurePosixPath("output-files", sha256(raw))


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


def build_aggregation_coordinator_claim(
    coordinator_actor_id: str,
    static_lock_sha256: str,
    reviewer_ids: frozenset[str],
) -> dict[str, Any]:
    coordinator_actor_id = require_production_runtime_actor(
        coordinator_actor_id,
        "aggregation coordinator actor ID",
        reviewer_ids,
    )
    if not isinstance(static_lock_sha256, str) or not HEX64.fullmatch(
        static_lock_sha256
    ):
        raise ProtocolError("aggregation coordinator claim has an invalid static lock")
    return {
        "schema_version": 1,
        "status": "CLAIMED",
        "coordinator_actor_id": coordinator_actor_id,
        "static_lock_sha256": static_lock_sha256,
    }


def validate_aggregation_coordinator_claim(
    value: Any,
    static_lock_sha256: str,
    reviewer_ids: frozenset[str],
) -> dict[str, Any]:
    claim = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "coordinator_actor_id",
            "static_lock_sha256",
        },
        "aggregation coordinator claim",
    )
    expected = build_aggregation_coordinator_claim(
        claim["coordinator_actor_id"], static_lock_sha256, reviewer_ids
    )
    if claim != expected:
        raise ProtocolError("aggregation coordinator claim identity/binding mismatch")
    return claim


def load_aggregation_coordinator_claim(
    state_root: Path,
    static_lock_sha256: str,
    reviewer_ids: frozenset[str],
) -> dict[str, Any]:
    path = state_root / "aggregation" / AGGREGATION_COORDINATOR_CLAIM
    claim = validate_aggregation_coordinator_claim(
        read_committed_json(path, "aggregation coordinator claim"),
        static_lock_sha256,
        reviewer_ids,
    )
    if path.read_bytes() != canonical_json_bytes(claim):
        raise ProtocolError("aggregation coordinator claim is not canonical JSON")
    return claim


def maybe_inject_fault(fault_after: str | None, point: str) -> None:
    if fault_after == point:
        raise InjectedFault(f"synthetic fault after {point}")


def fsync_directory(path: Path) -> None:
    fd = os.open(
        path,
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0),
    )
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def durable_mkdir(path: Path, mode: int = 0o700) -> None:
    """Create or recover a real directory chain and durably link each component."""

    path = Path(os.path.abspath(os.fspath(path)))
    chain: list[Path] = []
    cursor = path
    while True:
        chain.append(cursor)
        parent = cursor.parent
        if parent == cursor:
            break
        cursor = parent
    chain.reverse()
    missing_index = len(chain)
    for index, directory in enumerate(chain):
        try:
            info = directory.lstat()
        except FileNotFoundError:
            missing_index = index
            break
        except OSError as error:
            raise ProtocolError(
                f"directory chain component is unavailable: {directory}"
            ) from error
        if not stat.S_ISDIR(info.st_mode):
            raise ProtocolError(
                f"directory chain component is not a real directory: {directory}"
            )

    # The deepest visible component may be the result of a prior mkdir whose
    # self/parent fsync failed.  A retry must repair that namespace publication
    # even when no component remains to create.
    deepest_existing = chain[missing_index - 1]
    fsync_directory(deepest_existing)
    if deepest_existing.parent != deepest_existing:
        fsync_directory(deepest_existing.parent)

    for directory in chain[missing_index:]:
        try:
            os.mkdir(directory, mode=mode)
        except FileExistsError:
            pass
        try:
            info = directory.lstat()
        except OSError as error:
            raise ProtocolError(
                f"directory chain component is unavailable: {directory}"
            ) from error
        if not stat.S_ISDIR(info.st_mode):
            raise ProtocolError(
                f"directory chain component is not a real directory: {directory}"
            )
        fsync_directory(directory)
        fsync_directory(directory.parent)


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
    """Publish absent-or-complete immutable bytes with a hard-link CAS."""

    durable_mkdir(path.parent)
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
            os.fchmod(fd, 0o400)
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


def recover_exclusive_write_residues(state_root: Path) -> None:
    """Discard only unpublished private CAS files after a coordinator crash."""

    if not path_entry_exists(state_root):
        return
    residues: list[Path] = []
    for directory, directory_names, file_names in os.walk(
        state_root, topdown=True, followlinks=False
    ):
        directory_names.sort()
        file_names.sort()
        directory_path = Path(directory)
        if directory_path.is_symlink():
            raise ProtocolError(
                f"protocol state contains a symlinked directory: {directory_path}"
            )
        for name in file_names:
            if name.startswith(".exclusive-stage-"):
                path = directory_path / name
                if (
                    re.fullmatch(r"\.exclusive-stage-.+-[0-9a-f]{24}", name)
                    is None
                    or path.is_symlink()
                    or not path.is_file()
                ):
                    raise ProtocolError(
                        f"invalid exclusive-write recovery residue: {path}"
                    )
                residues.append(path)
    for path in residues:
        parent = path.parent
        original_mode = stat.S_IMODE(parent.lstat().st_mode)
        try:
            if not original_mode & stat.S_IWUSR:
                os.chmod(parent, original_mode | stat.S_IWUSR)
            path.unlink()
            fsync_directory(parent)
        finally:
            if stat.S_IMODE(parent.lstat().st_mode) != original_mode:
                os.chmod(parent, original_mode)
                fsync_directory(parent)
                fsync_directory(parent.parent)


def write_stage_file(path: Path, data: bytes) -> None:
    durable_mkdir(path.parent)
    exclusive_write(path, data)


def aggregation_stage_file_records(files: dict[str, bytes]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for path_text, data in sorted(files.items()):
        path_text = require_relative_file(path_text, "aggregation stage file path")
        if path_text == "stage-manifest.json":
            raise ProtocolError("aggregation stage payload cannot replace its manifest")
        if not isinstance(data, bytes):
            raise ProtocolError("aggregation stage payloads must be bytes")
        records.append(
            {
                "path": path_text,
                "size": len(data),
                "sha256": sha256(data),
            }
        )
    return records


def build_aggregation_stage_manifest(
    stage_id: str,
    files: dict[str, bytes],
    *,
    static_lock_sha256: str,
    coordinator_actor_id: str,
    prerequisite_stage_sha256: str | None,
    attempt_envelopes: dict[str, str],
) -> dict[str, Any]:
    if stage_id not in AGGREGATION_STAGE_ORDER:
        raise ProtocolError(f"unknown aggregation stage: {stage_id}")
    if not isinstance(static_lock_sha256, str) or not HEX64.fullmatch(
        static_lock_sha256
    ):
        raise ProtocolError("aggregation stage lacks a valid static-lock digest")
    coordinator_actor_id = require_production_actor_id(
        coordinator_actor_id, "aggregation coordinator actor ID"
    )
    if prerequisite_stage_sha256 is not None and (
        not isinstance(prerequisite_stage_sha256, str)
        or not HEX64.fullmatch(prerequisite_stage_sha256)
    ):
        raise ProtocolError("aggregation stage prerequisite digest is invalid")
    if not isinstance(attempt_envelopes, dict):
        raise ProtocolError("aggregation stage attempt inventory must be an object")
    attempts: list[dict[str, str]] = []
    for assignment_id, digest in sorted(attempt_envelopes.items()):
        require_safe_id(assignment_id, "aggregation stage attempt assignment")
        if not isinstance(digest, str) or not HEX64.fullmatch(digest):
            raise ProtocolError("aggregation stage attempt digest is invalid")
        attempts.append(
            {"assignment_id": assignment_id, "envelope_sha256": digest}
        )
    return {
        "schema_version": 1,
        "status": "COMPLETE",
        "algorithm": AGGREGATION_STAGE_MANIFEST_ALGORITHM,
        "stage_id": stage_id,
        "static_lock_sha256": static_lock_sha256,
        "coordinator_actor_id": coordinator_actor_id,
        "prerequisite_stage_sha256": prerequisite_stage_sha256,
        "attempt_envelopes": attempts,
        "files": aggregation_stage_file_records(files),
    }


def aggregation_stage_digest(manifest: dict[str, Any]) -> str:
    return sha256(canonical_json_bytes(manifest))


def validate_aggregation_terminal_failure(value: Any) -> dict[str, Any]:
    """Validate the canonical alternative terminal outcome shape."""

    terminal = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "outcome",
            "algorithm",
            "static_lock_sha256",
            "coordinator_actor_id",
            "blocked_stage_id",
            "prerequisite_stage_sha256",
            "attempt_envelopes",
            "failures",
        },
        "aggregation terminal failure",
    )
    if (
        terminal["schema_version"] != 1
        or terminal["status"] != "TERMINAL-FAILURE"
        or terminal["outcome"] != "ERROR"
        or terminal["algorithm"] != AGGREGATION_TERMINAL_FAILURE_ALGORITHM
        or not isinstance(terminal["static_lock_sha256"], str)
        or HEX64.fullmatch(terminal["static_lock_sha256"]) is None
        or terminal["blocked_stage_id"] not in AGGREGATION_STAGE_ORDER
    ):
        raise ProtocolError("aggregation terminal failure identity is invalid")
    require_production_actor_id(
        terminal["coordinator_actor_id"],
        "aggregation terminal-failure coordinator",
    )
    prerequisite = terminal["prerequisite_stage_sha256"]
    if prerequisite is not None and (
        not isinstance(prerequisite, str) or HEX64.fullmatch(prerequisite) is None
    ):
        raise ProtocolError("aggregation terminal-failure prerequisite is invalid")
    if not isinstance(terminal["attempt_envelopes"], list):
        raise ProtocolError("aggregation terminal-failure attempts must be a list")
    attempt_rows: list[dict[str, str]] = []
    for raw in terminal["attempt_envelopes"]:
        row = require_exact_keys(
            raw,
            {"assignment_id", "envelope_sha256"},
            "aggregation terminal-failure attempt",
        )
        require_safe_id(row["assignment_id"], "terminal-failure assignment")
        if (
            not isinstance(row["envelope_sha256"], str)
            or HEX64.fullmatch(row["envelope_sha256"]) is None
        ):
            raise ProtocolError("terminal-failure envelope digest is invalid")
        attempt_rows.append(row)
    if attempt_rows != sorted(attempt_rows, key=lambda row: row["assignment_id"]) or len(
        {row["assignment_id"] for row in attempt_rows}
    ) != len(attempt_rows):
        raise ProtocolError("terminal-failure attempts are not unique and sorted")
    if not isinstance(terminal["failures"], list) or not terminal["failures"]:
        raise ProtocolError("aggregation terminal failure has no failures")
    failure_rows: list[dict[str, Any]] = []
    for raw in terminal["failures"]:
        row = require_exact_keys(
            raw,
            {
                "assignment_id",
                "role",
                "envelope_sha256",
                "primary_output_present",
                "format_valid",
                "semantic_valid",
            },
            "aggregation terminal-failure record",
        )
        require_safe_id(row["assignment_id"], "terminal-failure assignment")
        if (
            row["role"] not in SEMANTIC_AGENT_ROLES
            or not isinstance(row["envelope_sha256"], str)
            or HEX64.fullmatch(row["envelope_sha256"]) is None
            or any(
                type(row[name]) is not bool
                for name in (
                    "primary_output_present",
                    "format_valid",
                    "semantic_valid",
                )
            )
        ):
            raise ProtocolError("aggregation terminal-failure record is invalid")
        failure_rows.append(row)
    if failure_rows != sorted(failure_rows, key=lambda row: row["assignment_id"]) or len(
        {row["assignment_id"] for row in failure_rows}
    ) != len(failure_rows):
        raise ProtocolError("terminal-failure records are not unique and sorted")
    attempts = {
        row["assignment_id"]: row["envelope_sha256"] for row in attempt_rows
    }
    if any(
        row["assignment_id"] not in attempts
        or attempts[row["assignment_id"]] != row["envelope_sha256"]
        for row in failure_rows
    ):
        raise ProtocolError("terminal failures are not bound to the attempt inventory")
    return terminal


def build_aggregation_terminal_failure(
    *,
    blocked_stage_id: str,
    static_lock_sha256: str,
    coordinator_actor_id: str,
    prerequisite_stage_sha256: str | None,
    attempts: dict[str, dict[str, Any]],
    cumulative_assignments: set[str],
    failure_assignments: set[str],
) -> dict[str, Any]:
    """Build one order-independent terminal error at a sealed phase barrier."""

    if not failure_assignments or not failure_assignments <= cumulative_assignments:
        raise ProtocolError("aggregation terminal failure set is invalid")
    attempt_envelopes = sealed_attempt_envelopes(
        attempts, cumulative_assignments
    )
    failures: list[dict[str, Any]] = []
    for assignment_id in sorted(failure_assignments):
        attempt = attempts[assignment_id]
        pointer = attempt["pointer"]
        if not isinstance(pointer, dict):
            raise ProtocolError("terminal failure lacks a canonical pointer")
        failures.append(
            {
                "assignment_id": assignment_id,
                "role": attempt["launch"]["role"],
                "envelope_sha256": pointer["envelope_sha256"],
                "primary_output_present": attempt["primary_bytes"] is not None,
                "format_valid": pointer["format_valid"],
                "semantic_valid": pointer["semantic_valid"],
            }
        )
    return validate_aggregation_terminal_failure(
        {
            "schema_version": 1,
            "status": "TERMINAL-FAILURE",
            "outcome": "ERROR",
            "algorithm": AGGREGATION_TERMINAL_FAILURE_ALGORITHM,
            "static_lock_sha256": static_lock_sha256,
            "coordinator_actor_id": coordinator_actor_id,
            "blocked_stage_id": blocked_stage_id,
            "prerequisite_stage_sha256": prerequisite_stage_sha256,
            "attempt_envelopes": [
                {
                    "assignment_id": assignment_id,
                    "envelope_sha256": digest,
                }
                for assignment_id, digest in sorted(attempt_envelopes.items())
            ],
            "failures": failures,
        }
    )


def publish_or_verify_aggregation_terminal_failure(
    aggregation_root: Path, expected: dict[str, Any]
) -> dict[str, Any]:
    """Publish an absent-or-identical immutable terminal error record."""

    expected = validate_aggregation_terminal_failure(expected)
    path = aggregation_root / AGGREGATION_TERMINAL_FAILURE
    expected_bytes = canonical_json_bytes(expected)
    if path.exists() or path.is_symlink():
        actual = validate_aggregation_terminal_failure(
            read_committed_json(path, "aggregation terminal failure")
        )
        if actual != expected or path.read_bytes() != expected_bytes:
            raise ProtocolError("aggregation terminal failure is not the exact derivation")
        fsync_directory(path.parent)
        return actual
    try:
        exclusive_write(path, expected_bytes)
    except FileExistsError:
        pass
    except BaseException:
        if not path_entry_exists(path):
            raise
    actual = validate_aggregation_terminal_failure(
        read_committed_json(path, "aggregation terminal failure")
    )
    if actual != expected or path.read_bytes() != expected_bytes:
        raise ProtocolError("aggregation terminal failure lost its publication race")
    fsync_directory(path.parent)
    return actual


def _validate_aggregation_stage_tree(
    stage_root: Path,
    expected_files: dict[str, bytes],
    expected_manifest: dict[str, Any],
) -> dict[str, Any]:
    if stage_root.is_symlink() or not stage_root.is_dir():
        raise ProtocolError(f"aggregation stage is not a real directory: {stage_root}")
    expected_paths = set(expected_files) | {"stage-manifest.json"}
    expected_directories: set[str] = set()
    for path_text in expected_paths:
        for parent in PurePosixPath(path_text).parents:
            if parent.as_posix() not in ("", "."):
                expected_directories.add(parent.as_posix())
    actual_paths: set[str] = set()
    actual_directories: set[str] = set()
    for path in stage_root.rglob("*"):
        relative = path.relative_to(stage_root).as_posix()
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ProtocolError(f"unsupported aggregation stage entry: {relative}")
        if path.is_dir():
            actual_directories.add(relative)
        else:
            actual_paths.add(relative)
            if path.lstat().st_mode & 0o222:
                raise ProtocolError(f"aggregation stage file is mutable: {relative}")
    if actual_paths != expected_paths:
        raise ProtocolError(
            "aggregation stage file inventory is not exact; "
            f"missing={sorted(expected_paths - actual_paths)}, "
            f"extra={sorted(actual_paths - expected_paths)}"
        )
    if actual_directories != expected_directories:
        raise ProtocolError(
            "aggregation stage directory inventory is not exact; "
            f"missing={sorted(expected_directories - actual_directories)}, "
            f"extra={sorted(actual_directories - expected_directories)}"
        )
    for path_text, expected_bytes in expected_files.items():
        path = stage_root / Path(*PurePosixPath(path_text).parts)
        if path.read_bytes() != expected_bytes:
            raise ProtocolError(f"aggregation stage payload drifted: {path_text}")
    manifest_path = stage_root / "stage-manifest.json"
    manifest_bytes = manifest_path.read_bytes()
    manifest = strict_json_loads(manifest_bytes, str(manifest_path))
    if (
        manifest != expected_manifest
        or manifest_bytes != canonical_json_bytes(expected_manifest)
    ):
        raise ProtocolError("aggregation stage manifest is not the exact derivation")
    for directory in (stage_root, *(path for path in stage_root.rglob("*") if path.is_dir())):
        if directory.lstat().st_mode & 0o222:
            raise ProtocolError(f"aggregation stage directory is mutable: {directory}")
    return manifest


def _discard_private_aggregation_stage(stage: Path) -> None:
    """Discard only one protocol-owned, unpublished stage directory."""

    if not stage.exists() and not stage.is_symlink():
        return
    if stage.is_symlink() or not stage.is_dir():
        raise ProtocolError(f"private aggregation stage is not a real directory: {stage}")
    for directory, directory_names, _file_names in os.walk(
        stage, topdown=True, followlinks=False
    ):
        directory_names.sort()
        directory_path = Path(directory)
        if directory_path.is_symlink():
            raise ProtocolError(
                f"private aggregation stage contains a symlinked directory: {directory_path}"
            )
        os.chmod(directory_path, 0o700)
    shutil.rmtree(stage)
    fsync_directory(stage.parent)


def _publish_directory_no_replace(stage: Path, output: Path) -> None:
    """Atomically publish one same-directory tree without replacement."""

    if stage.parent != output.parent:
        raise ProtocolError("aggregation publication requires a same-directory stage")
    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise ProtocolError(
            "aggregation publication requires renameat2(RENAME_NOREPLACE)"
        )
    renameat2.argtypes = [
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_int,
        ctypes.c_char_p,
        ctypes.c_uint,
    ]
    renameat2.restype = ctypes.c_int
    result = renameat2(
        -100,
        os.fsencode(stage),
        -100,
        os.fsencode(output),
        1,
    )
    if result != 0:
        error = ctypes.get_errno()
        if error == errno.EEXIST:
            raise FileExistsError(output)
        raise ProtocolError(
            f"atomic aggregation publication failed: {os.strerror(error)}"
        )
    fsync_directory(output.parent)


def publish_or_verify_aggregation_stage(
    aggregation_root: Path,
    stage_id: str,
    files: dict[str, bytes],
    *,
    static_lock_sha256: str,
    coordinator_actor_id: str,
    prerequisite_stage_sha256: str | None,
    attempt_envelopes: dict[str, str],
) -> dict[str, Any]:
    """Idempotently build, harden, and atomically publish one stage tree."""

    expected_manifest = build_aggregation_stage_manifest(
        stage_id,
        files,
        static_lock_sha256=static_lock_sha256,
        coordinator_actor_id=coordinator_actor_id,
        prerequisite_stage_sha256=prerequisite_stage_sha256,
        attempt_envelopes=attempt_envelopes,
    )
    stage_root = (
        aggregation_root / "final"
        if stage_id == "final"
        else aggregation_root / "derived" / stage_id
    )
    stage_parent = stage_root.parent
    durable_mkdir(stage_parent)
    if stage_parent.is_symlink() or not stage_parent.is_dir():
        raise ProtocolError("aggregation stage parent is not a real directory")
    pending = stage_parent / f"{AGGREGATION_PENDING_STAGE_PREFIX}{stage_id}"
    if stage_root.exists() or stage_root.is_symlink():
        if pending.exists() or pending.is_symlink():
            _discard_private_aggregation_stage(pending)
        manifest = _validate_aggregation_stage_tree(
            stage_root, files, expected_manifest
        )
        fsync_directory(stage_parent)
        return manifest
    if pending.exists() or pending.is_symlink():
        _discard_private_aggregation_stage(pending)
    os.mkdir(pending, mode=0o700)
    try:
        for path_text, expected_bytes in sorted(files.items()):
            path = pending / Path(*PurePosixPath(path_text).parts)
            write_stage_file(path, expected_bytes)
        write_stage_file(
            pending / "stage-manifest.json",
            canonical_json_bytes(expected_manifest),
        )
        harden_tree_read_only(pending)
        _validate_aggregation_stage_tree(pending, files, expected_manifest)
        try:
            _publish_directory_no_replace(pending, stage_root)
        except FileExistsError:
            manifest = _validate_aggregation_stage_tree(
                stage_root, files, expected_manifest
            )
            fsync_directory(stage_parent)
            return manifest
        except BaseException:
            if not path_entry_exists(stage_root):
                raise
            manifest = _validate_aggregation_stage_tree(
                stage_root, files, expected_manifest
            )
            fsync_directory(stage_parent)
            return manifest
        manifest = _validate_aggregation_stage_tree(
            stage_root, files, expected_manifest
        )
        fsync_directory(stage_parent)
        return manifest
    finally:
        if pending.exists() or pending.is_symlink():
            _discard_private_aggregation_stage(pending)


def aggregation_stage_file(
    aggregation_root: Path, stage_id: str, relative_path: str
) -> Path:
    if stage_id not in AGGREGATION_STAGE_ORDER:
        raise ProtocolError(f"unknown aggregation stage: {stage_id}")
    relative_path = require_relative_file(
        relative_path, "aggregation stage lookup path"
    )
    stage_root = (
        aggregation_root / "final"
        if stage_id == "final"
        else aggregation_root / "derived" / stage_id
    )
    manifest = validate_committed_aggregation_stage(aggregation_root, stage_id)
    path = stage_root / Path(*PurePosixPath(relative_path).parts)
    if not path.is_file() or path.is_symlink() or path.lstat().st_mode & 0o222:
        raise ProtocolError(
            f"aggregation stage file is absent or mutable: {stage_id}/{relative_path}"
        )
    record = next(
        (item for item in manifest["files"] if item["path"] == relative_path),
        None,
    )
    data = path.read_bytes()
    if (
        record is None
        or record["size"] != len(data)
        or record["sha256"] != sha256(data)
    ):
        raise ProtocolError(
            f"aggregation stage manifest does not authorize file: {stage_id}/{relative_path}"
        )
    return path


def _aggregation_stage_root(aggregation_root: Path, stage_id: str) -> Path:
    return (
        aggregation_root / "final"
        if stage_id == "final"
        else aggregation_root / "derived" / stage_id
    )


def recover_private_aggregation_stages(aggregation_root: Path) -> None:
    """Discard deterministic unpublished trees left by an interrupted publisher."""

    for stage_id in AGGREGATION_STAGE_ORDER:
        stage_root = _aggregation_stage_root(aggregation_root, stage_id)
        pending = stage_root.parent / f"{AGGREGATION_PENDING_STAGE_PREFIX}{stage_id}"
        if pending.exists() or pending.is_symlink():
            _discard_private_aggregation_stage(pending)


def validate_aggregation_directory_inventory(
    aggregation_root: Path,
    *,
    require_final: bool,
) -> tuple[str, ...]:
    """Require the exact committed stage prefix and no unpublished siblings."""

    if aggregation_root.is_symlink() or not aggregation_root.is_dir():
        raise ProtocolError("aggregation root is not a real directory")
    allowed_root = {
        AGGREGATION_COORDINATOR_CLAIM,
        AGGREGATION_TERMINAL_FAILURE,
        "derived",
        "final",
    }
    unexpected_root = {
        path.name for path in aggregation_root.iterdir()
    } - allowed_root
    if unexpected_root:
        raise ProtocolError(
            f"aggregation root contains unexpected entries: {sorted(unexpected_root)}"
        )
    derived_root = aggregation_root / "derived"
    committed: tuple[str, ...]
    if path_entry_exists(derived_root):
        if derived_root.is_symlink() or not derived_root.is_dir():
            raise ProtocolError("aggregation derived root is not a real directory")
        names: list[str] = []
        for path in derived_root.iterdir():
            if path.is_symlink() or not path.is_dir():
                raise ProtocolError("aggregation derived root has a non-directory entry")
            names.append(path.name)
        expected_order = AGGREGATION_STAGE_ORDER[:-1]
        name_set = set(names)
        if len(name_set) != len(names) or not name_set <= set(expected_order):
            raise ProtocolError(
                f"aggregation derived stage inventory is invalid: {sorted(names)}"
            )
        prefix_length = len(name_set)
        committed = tuple(expected_order[:prefix_length])
        if name_set != set(committed):
            raise ProtocolError("aggregation derived stages are not an ordered prefix")
    else:
        committed = ()
    final_root = aggregation_root / "final"
    terminal_path = aggregation_root / AGGREGATION_TERMINAL_FAILURE
    if terminal_path.exists() or terminal_path.is_symlink():
        if final_root.exists() or final_root.is_symlink():
            raise ProtocolError(
                "aggregation cannot contain both final and terminal-failure outcomes"
            )
        validate_aggregation_terminal_failure(
            read_committed_json(terminal_path, "aggregation terminal failure")
        )
    if final_root.exists() or final_root.is_symlink():
        if final_root.is_symlink() or not final_root.is_dir():
            raise ProtocolError("final aggregation stage is not a real directory")
        if committed != AGGREGATION_STAGE_ORDER[:-1]:
            raise ProtocolError("final aggregation stage exists before every prerequisite stage")
        committed = (*committed, "final")
    if require_final and committed != AGGREGATION_STAGE_ORDER:
        raise ProtocolError("complete aggregation does not contain the exact stage chain")
    return committed


def validate_committed_aggregation_stage(
    aggregation_root: Path,
    stage_id: str,
) -> dict[str, Any]:
    """Validate one stage's immutable manifest and exact self-contained byte tree."""

    stage_root = _aggregation_stage_root(aggregation_root, stage_id)
    manifest_path = stage_root / "stage-manifest.json"
    manifest = require_exact_keys(
        read_committed_json(manifest_path, f"{stage_id} manifest"),
        {
            "schema_version",
            "status",
            "algorithm",
            "stage_id",
            "static_lock_sha256",
            "coordinator_actor_id",
            "prerequisite_stage_sha256",
            "attempt_envelopes",
            "files",
        },
        f"{stage_id} manifest",
    )
    if manifest_path.read_bytes() != canonical_json_bytes(manifest):
        raise ProtocolError(f"{stage_id} manifest is not canonical JSON")
    payloads: dict[str, bytes] = {}
    for record in manifest.get("files", []):
        if not isinstance(record, dict) or set(record) != {"path", "size", "sha256"}:
            raise ProtocolError(f"{stage_id} manifest file record is invalid")
        path_text = require_relative_file(
            record["path"], f"{stage_id} manifest file path"
        )
        if path_text in payloads:
            raise ProtocolError(f"{stage_id} manifest repeats a file path")
        path = stage_root / Path(*PurePosixPath(path_text).parts)
        if path.is_symlink() or not path.is_file():
            raise ProtocolError(f"{stage_id} manifest file is missing: {path_text}")
        data = path.read_bytes()
        if record["size"] != len(data) or record["sha256"] != sha256(data):
            raise ProtocolError(f"{stage_id} manifest file binding mismatch: {path_text}")
        payloads[path_text] = data
    expected = build_aggregation_stage_manifest(
        stage_id,
        payloads,
        static_lock_sha256=manifest.get("static_lock_sha256"),
        coordinator_actor_id=manifest.get("coordinator_actor_id"),
        prerequisite_stage_sha256=manifest.get("prerequisite_stage_sha256"),
        attempt_envelopes={
            row["assignment_id"]: row["envelope_sha256"]
            for row in manifest.get("attempt_envelopes", [])
            if isinstance(row, dict)
            and set(row) == {"assignment_id", "envelope_sha256"}
        },
    )
    return _validate_aggregation_stage_tree(stage_root, payloads, expected)


def validate_aggregation_stage_chain(
    aggregation_root: Path,
    committed_stages: tuple[str, ...],
    coordinator_claim: dict[str, Any],
) -> list[dict[str, Any]]:
    """Join every committed manifest to the claim and its exact predecessor."""

    manifests: list[dict[str, Any]] = []
    prerequisite: str | None = None
    for stage_id in committed_stages:
        manifest = validate_committed_aggregation_stage(
            aggregation_root, stage_id
        )
        if (
            manifest["static_lock_sha256"]
            != coordinator_claim["static_lock_sha256"]
            or manifest["coordinator_actor_id"]
            != coordinator_claim["coordinator_actor_id"]
            or manifest["prerequisite_stage_sha256"] != prerequisite
        ):
            raise ProtocolError(
                f"aggregation stage chain/claim binding failed: {stage_id}"
            )
        manifests.append(manifest)
        prerequisite = aggregation_stage_digest(manifest)
    return manifests


def validate_aggregation_attempt_bindings(
    committed_stages: tuple[str, ...],
    manifests: list[dict[str, Any]],
    slot_results: list[dict[str, Any]],
    terminal: dict[str, Any] | None,
) -> None:
    """Join stage/terminal inventories to the authoritative sealed envelopes."""

    if len(committed_stages) != len(manifests):
        raise ProtocolError("aggregation stage manifest inventory length drifted")
    sealed = {
        row["slot_id"]: row["envelope_sha256"]
        for row in slot_results
        if row["status"] == "SEALED"
    }
    all_slot_ids = {row["slot_id"] for row in slot_results}
    report_ids = {f"r{index:03d}" for index in range(1, 121)}
    scorer_ids = {f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS}
    consistency_ids = {
        f"{mode}-{reviewer}"
        for mode in MODES
        for reviewer in CONSISTENCY_REVIEWERS
    }
    expected_sets: dict[str, set[str]] = {
        "01-report-products": report_ids,
        "02-scorer-products": report_ids | scorer_ids,
        "03-consistency-products": report_ids | scorer_ids | consistency_ids,
    }
    manifest_by_stage = {
        stage_id: manifest
        for stage_id, manifest in zip(committed_stages, manifests, strict=True)
    }
    adjudicator_ids: set[str] = set()
    stage_03 = manifest_by_stage.get("03-consistency-products")
    if stage_03 is not None:
        for record in stage_03["files"]:
            match = re.fullmatch(
                r"launches/adjudication/([EVFPBLRQ]-a1)\.json",
                record["path"],
            )
            if match:
                adjudicator_ids.add(match.group(1))
    expected_sets["04-score-products"] = (
        expected_sets["03-consistency-products"] | adjudicator_ids
    )
    expected_sets["05-materiality-products"] = (
        expected_sets["04-score-products"] | set(MATERIALITY_REVIEWERS)
    )
    materiality_adjudicator_ids: set[str] = set()
    stage_05 = manifest_by_stage.get("05-materiality-products")
    if stage_05 is not None and any(
        record["path"] == "launches/materiality/ma1.json"
        for record in stage_05["files"]
    ):
        materiality_adjudicator_ids.add("ma1")
    expected_sets["final"] = (
        expected_sets["05-materiality-products"]
        | materiality_adjudicator_ids
    )
    for stage_id, manifest in manifest_by_stage.items():
        attempt_map = {
            row["assignment_id"]: row["envelope_sha256"]
            for row in manifest["attempt_envelopes"]
        }
        if set(attempt_map) != expected_sets[stage_id] or any(
            sealed.get(assignment_id) != digest
            for assignment_id, digest in attempt_map.items()
        ):
            raise ProtocolError(
                f"aggregation stage attempt inventory is not authoritative: {stage_id}"
            )
    frontier_by_stage = {
        None: report_ids,
        "01-report-products": expected_sets["01-report-products"] | scorer_ids,
        "02-scorer-products": expected_sets["02-scorer-products"]
        | consistency_ids,
        "03-consistency-products": expected_sets["03-consistency-products"]
        | adjudicator_ids,
        "04-score-products": expected_sets["04-score-products"]
        | set(MATERIALITY_REVIEWERS),
        "05-materiality-products": expected_sets["05-materiality-products"]
        | materiality_adjudicator_ids,
        "final": expected_sets["final"],
    }
    current_stage = committed_stages[-1] if committed_stages else None
    if not all_slot_ids <= frontier_by_stage[current_stage]:
        raise ProtocolError(
            "runtime slot inventory contains a premature or unknown assignment"
        )
    if (
        committed_stages
        and committed_stages[-1] == "final"
        and (
            set(sealed) != expected_sets["final"]
            or all_slot_ids != expected_sets["final"]
        )
    ):
        raise ProtocolError("final aggregation does not bind every sealed attempt")
    result_by_slot = {row["slot_id"]: row for row in slot_results}
    phase_assignments_by_stage = {
        "01-report-products": report_ids,
        "02-scorer-products": scorer_ids,
        "03-consistency-products": consistency_ids,
        "04-score-products": adjudicator_ids,
        "05-materiality-products": set(MATERIALITY_REVIEWERS),
        "final": materiality_adjudicator_ids,
    }

    def phase_failure_ids(stage_id: str) -> set[str]:
        return {
            assignment_id
            for assignment_id in phase_assignments_by_stage[stage_id]
            if (
                not result_by_slot[assignment_id]["primary_output_present"]
                or not result_by_slot[assignment_id]["semantic_valid"]
                or (
                    stage_id != "01-report-products"
                    and not result_by_slot[assignment_id]["format_valid"]
                )
            )
        }

    for stage_id in committed_stages:
        if phase_failure_ids(stage_id):
            raise ProtocolError(
                f"committed aggregation stage has a terminal phase failure: {stage_id}"
            )
    if terminal is None:
        return
    blocked_stage = terminal["blocked_stage_id"]
    blocked_index = AGGREGATION_STAGE_ORDER.index(blocked_stage)
    if committed_stages != AGGREGATION_STAGE_ORDER[:blocked_index]:
        raise ProtocolError("terminal failure does not follow the exact stage prefix")
    expected_prerequisite = (
        aggregation_stage_digest(manifests[-1]) if manifests else None
    )
    if terminal["prerequisite_stage_sha256"] != expected_prerequisite:
        raise ProtocolError("terminal failure prerequisite-stage binding drifted")
    phase_assignments = phase_assignments_by_stage[blocked_stage]
    prior_assignments = (
        expected_sets[AGGREGATION_STAGE_ORDER[blocked_index - 1]]
        if blocked_index
        else set()
    )
    expected_attempts = prior_assignments | phase_assignments
    terminal_attempts = {
        row["assignment_id"]: row["envelope_sha256"]
        for row in terminal["attempt_envelopes"]
    }
    if (
        set(terminal_attempts) != expected_attempts
        or terminal_attempts != sealed
        or all_slot_ids != expected_attempts
    ):
        raise ProtocolError("terminal failure attempt inventory is not exact")
    expected_failure_ids = phase_failure_ids(blocked_stage)
    expected_failures = [
        {
            "assignment_id": assignment_id,
            "role": result_by_slot[assignment_id]["role"],
            "envelope_sha256": result_by_slot[assignment_id]["envelope_sha256"],
            "primary_output_present": result_by_slot[assignment_id][
                "primary_output_present"
            ],
            "format_valid": result_by_slot[assignment_id]["format_valid"],
            "semantic_valid": result_by_slot[assignment_id]["semantic_valid"],
        }
        for assignment_id in sorted(expected_failure_ids)
    ]
    if not expected_failures or terminal["failures"] != expected_failures:
        raise ProtocolError("terminal failure records are not the exact phase failures")


@contextlib.contextmanager
def operation_lock(state_root: Path) -> Iterator[None]:
    durable_mkdir(state_root)
    lock_path = state_root / ".protocol.lock"
    flags = (
        os.O_RDWR
        | os.O_CREAT
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_NONBLOCK", 0)
    )
    try:
        fd = os.open(lock_path, flags, 0o600)
    except OSError as error:
        raise ProtocolError("protocol lock is not a writable regular file") from error
    try:
        opened = os.fstat(fd)
        if not stat.S_ISREG(opened.st_mode):
            raise ProtocolError("protocol lock is not a regular file")
        fcntl.flock(fd, fcntl.LOCK_EX)
        listed = os.stat(lock_path, follow_symlinks=False)
        if (
            not stat.S_ISREG(listed.st_mode)
            or (listed.st_dev, listed.st_ino) != (opened.st_dev, opened.st_ino)
        ):
            raise ProtocolError("protocol lock path changed during acquisition")
        yield
    finally:
        try:
            fcntl.flock(fd, fcntl.LOCK_UN)
        except OSError:
            pass
        os.close(fd)


@contextlib.contextmanager
def production_custody_lock(
    static_root: Path, external_commitment_path: Path | None
) -> Iterator[tuple[Path, Path]]:
    """Serialize one trusted operation and detect ordinary root/path replacement.

    The separately custodied commitment is the cooperative lock object.  This
    detects path identity drift around an operation, while the documented
    coordinator-custody premise still excludes an attacker that ignores the
    lock or performs an ABA replacement under the same UID.
    """

    if external_commitment_path is None:
        raise ProtocolError("production operation requires an external commitment")
    root = Path(os.path.abspath(os.fspath(static_root)))
    commitment = Path(os.path.abspath(os.fspath(external_commitment_path)))
    if (
        root.is_symlink()
        or not root.is_dir()
        or commitment.is_symlink()
        or not commitment.is_file()
        or is_within(commitment, root)
    ):
        raise ProtocolError("production custody paths are not disjoint regular paths")
    flags = (
        os.O_RDONLY
        | getattr(os, "O_NOFOLLOW", 0)
        | getattr(os, "O_CLOEXEC", 0)
    )
    fd = os.open(commitment, flags)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX)
        commitment_before = os.fstat(fd)
        commitment_path_before = os.stat(commitment, follow_symlinks=False)
        root_before = os.stat(root, follow_symlinks=False)
        identity = lambda info: (info.st_dev, info.st_ino)
        if (
            not stat.S_ISREG(commitment_before.st_mode)
            or identity(commitment_before) != identity(commitment_path_before)
            or not stat.S_ISDIR(root_before.st_mode)
        ):
            raise ProtocolError("production custody identity is invalid")
        try:
            yield root, commitment
        finally:
            # Run the closing identity check even when the operation exits by
            # exception.  Some successful read-only APIs use an internal
            # exception to return DERIVABLE progress, and must not bypass the
            # custody boundary on that path.
            try:
                commitment_after = os.fstat(fd)
                commitment_path_after = os.stat(commitment, follow_symlinks=False)
                root_after = os.stat(root, follow_symlinks=False)
            except OSError as error:
                raise ProtocolError(
                    "production custody path disappeared during operation"
                ) from error
            if (
                identity(commitment_before) != identity(commitment_after)
                or identity(commitment_before) != identity(commitment_path_after)
                or identity(root_before) != identity(root_after)
            ):
                raise ProtocolError(
                    "production custody identity changed during operation"
                )
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def byte_tree_digest(root: Path) -> str:
    """Hash every directory and regular file with unambiguous framing."""

    try:
        root_before = root.lstat()
    except OSError as error:
        raise ProtocolError(
            f"immutable envelope root is unavailable: {root}"
        ) from error
    if not stat.S_ISDIR(root_before.st_mode):
        raise ProtocolError(
            f"immutable envelope root is not a real directory: {root}"
        )
    hasher = hashlib.sha256()
    records: list[tuple[bytes, bytes, bytes]] = []
    for directory, directory_names, file_names in os.walk(root, followlinks=False):
        directory_names.sort()
        file_names.sort()
        directory_path = Path(directory)
        for name in directory_names:
            path = directory_path / name
            if path.is_symlink():
                raise ProtocolError(f"symlink in immutable envelope: {path}")
            relative = path.relative_to(root).as_posix().encode("utf-8")
            records.append((b"D", relative, b""))
        for name in file_names:
            path = directory_path / name
            info = path.lstat()
            if not stat.S_ISREG(info.st_mode):
                raise ProtocolError(f"non-regular file in immutable envelope: {path}")
            relative = path.relative_to(root).as_posix().encode("utf-8")
            records.append((b"F", relative, path.read_bytes()))
    records.sort(key=lambda record: (record[1], record[0]))
    hasher.update(b"V5_ENVELOPE_BYTE_TREE_V2\0")
    hasher.update(len(records).to_bytes(8, "big"))
    for kind, relative, data in records:
        hasher.update(kind)
        hasher.update(len(relative).to_bytes(8, "big"))
        hasher.update(relative)
        hasher.update(len(data).to_bytes(8, "big"))
        hasher.update(data)
    try:
        root_after = root.lstat()
    except OSError as error:
        raise ProtocolError(
            f"immutable envelope root disappeared during hashing: {root}"
        ) from error
    if (
        not stat.S_ISDIR(root_after.st_mode)
        or (root_before.st_dev, root_before.st_ino)
        != (root_after.st_dev, root_after.st_ino)
    ):
        raise ProtocolError(
            f"immutable envelope root changed during hashing: {root}"
        )
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
) -> dict[str, Any]:
    manifest = validate_atom_manifest(atom_manifest)
    first = validate_direct_score(first, manifest, defect_rules, "s1", first_input_packet)
    second = validate_direct_score(second, manifest, defect_rules, "s2", second_input_packet)
    input_digests = {
        "score_s1_sha256": sha256(canonical_json_bytes(first)),
        "score_s2_sha256": sha256(canonical_json_bytes(second)),
        "score_input_s1_sha256": sha256(canonical_json_bytes(first_input_packet)),
        "score_input_s2_sha256": sha256(canonical_json_bytes(second_input_packet)),
        "atom_manifest_sha256": sha256(canonical_json_bytes(manifest)),
        "defect_rules_sha256": sha256(canonical_json_bytes(validate_defect_rules(defect_rules))),
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
        },
    )
    return {
        "schema_version": 2,
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
        packet["schema_version"] != 2
        or packet["status"] != "CONSISTENCY-INPUT-PACKET"
        or packet["mode"] not in MODES
    ):
        raise ProtocolError("consistency packet identity/status mismatch")
    digests = require_exact_keys(
        packet["input_digests"],
        {
            "score_s1_sha256",
            "score_s2_sha256",
            "score_input_s1_sha256",
            "score_input_s2_sha256",
            "atom_manifest_sha256",
            "defect_rules_sha256",
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
        "score_input_s1_sha256": "score-inputs/s1.json",
        "score_input_s2_sha256": "score-inputs/s2.json",
        "atom_manifest_sha256": "resources/atom-manifest.json",
        "defect_rules_sha256": "resources/defect-rules.json",
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
    if {record["path"] for record in tree["files"]} != {
        "scores/s1.json",
        "scores/s2.json",
        "score-inputs/s1.json",
        "score-inputs/s2.json",
        "resources/atom-manifest.json",
        "resources/defect-rules.json",
    }:
        raise ProtocolError("consistency packet tree path set is not exact")
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
        "score_input_s1_sha256": sha256(canonical_json_bytes(first_input_packet)),
        "score_input_s2_sha256": sha256(canonical_json_bytes(second_input_packet)),
        "consistency_c1_sha256": sha256(canonical_json_bytes(consistency_first)),
        "consistency_c2_sha256": sha256(canonical_json_bytes(consistency_second)),
        "consistency_packet_sha256": sha256(canonical_json_bytes(consistency_packet)),
        "atom_manifest_sha256": sha256(canonical_json_bytes(manifest)),
        "defect_rules_sha256": sha256(canonical_json_bytes(validate_defect_rules(defect_rules))),
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
        },
    )
    return {
        "schema_version": 3,
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
        packet["schema_version"] != 3
        or packet["status"] != "ADJUDICATION-PACKET"
        or packet["mode"] not in MODES
    ):
        raise ProtocolError("adjudication packet identity/status mismatch")
    digests = require_exact_keys(
        packet["input_digests"],
        {
            "score_s1_sha256",
            "score_s2_sha256",
            "score_input_s1_sha256",
            "score_input_s2_sha256",
            "consistency_c1_sha256",
            "consistency_c2_sha256",
            "consistency_packet_sha256",
            "atom_manifest_sha256",
            "defect_rules_sha256",
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
        "score_input_s1_sha256": "score-inputs/s1.json",
        "score_input_s2_sha256": "score-inputs/s2.json",
        "consistency_c1_sha256": "consistency/c1.json",
        "consistency_c2_sha256": "consistency/c2.json",
        "consistency_packet_sha256": "consistency/input.json",
        "atom_manifest_sha256": "resources/atom-manifest.json",
        "defect_rules_sha256": "resources/defect-rules.json",
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
    if {record["path"] for record in tree["files"]} != {
        "scores/s1.json",
        "scores/s2.json",
        "score-inputs/s1.json",
        "score-inputs/s2.json",
        "consistency/input.json",
        "consistency/c1.json",
        "consistency/c2.json",
        "resources/atom-manifest.json",
        "resources/defect-rules.json",
    }:
        raise ProtocolError("adjudication packet tree path set is not exact")
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
        or rules["rules_version"] != "v5-diagnostic-aggregate-v2"
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
            "kind": "authenticated_oracle_review_closure_v2",
            "population": "TWO_SOURCE_ORACLE_REVIEWS_AND_ONE_SNAPSHOT_COVERAGE_REVIEW",
            "source_review_kind": "INDEPENDENT_ORACLE",
            "source_review_count": 2,
            "snapshot_hook_id": "H-VALIDATE-ORACLE-COVERAGE",
            "required_status": "PASS",
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
            "kind": "authenticated_coherence_review_v2",
            "population": "ONE_SOURCE_COHERENCE_REVIEW",
            "source_review_kind": "COHERENCE",
            "source_review_count": 1,
            "required_status": "PASS",
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
    if expected_status not in DIAGNOSTIC_CONTRACT_VERSIONS:
        raise ProtocolError("root inventory expected status is invalid")
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
        != DIAGNOSTIC_CONTRACT_VERSIONS[expected_status]
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
        != DIAGNOSTIC_CONTRACT_VERSIONS[expected_status]
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
    final_root = static_root / "runtime" / "state" / "aggregation" / "final"
    manifest = read_committed_json(
        final_root / "stage-manifest.json", "final aggregation stage manifest"
    )
    coordinator_actor_id = require_production_actor_id(
        manifest.get("coordinator_actor_id"), "aggregation coordinator actor ID"
    )
    receipt_root = final_root / "integration-receipts"
    if (
        not receipt_root.is_dir()
        or receipt_root.is_symlink()
        or receipt_root.lstat().st_mode & 0o222
    ):
        raise ProtocolError("bound aggregate receipt directory must be immutable")
    expected_receipts = build_bound_aggregate_receipts(
        aggregate, coordinator_actor_id
    )
    expected_names = {f"{hook_id}.json" for hook_id in POSTLOCK_RECEIPT_HOOK_IDS}
    if {path.name for path in receipt_root.iterdir()} != expected_names:
        raise ProtocolError("bound aggregate receipt file set is not exact")
    receipt_digests: dict[str, str] = {}
    for hook_id in POSTLOCK_RECEIPT_HOOK_IDS:
        path = receipt_root / f"{hook_id}.json"
        expected_bytes = canonical_json_bytes(expected_receipts[hook_id])
        if (
            read_committed_json(path, f"post-lock receipt {hook_id}")
            != expected_receipts[hook_id]
            or path.read_bytes() != expected_bytes
        ):
            raise ProtocolError(
                f"post-lock receipt is not the exact derivation: {hook_id}"
            )
        receipt_digests[hook_id] = sha256(expected_bytes)
    return receipt_digests



def evaluate_bound_gates(
    static_root: Path, external_commitment_path: Path | None = None
) -> dict[str, Any]:
    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        return _evaluate_bound_gates_under_custody(root, commitment)


def _evaluate_bound_gates_under_custody(
    static_root: Path, external_commitment_path: Path
) -> dict[str, Any]:
    root, static_lock, reviewer_ids, review_evidence = (
        load_verified_static_bundle_with_review_evidence(
            static_root, external_commitment_path
        )
    )
    rederived = _derive_aggregate_context_from_verified(
        root, static_lock, reviewer_ids, review_evidence
    )
    aggregate_path = (
        root
        / "runtime"
        / "state"
        / "aggregation"
        / "final"
        / "aggregate-context.json"
    )
    aggregate = validate_aggregate_context_document(
        read_committed_json(aggregate_path, "stored aggregate context")
    )
    if aggregate != rederived:
        raise ProtocolError("stored aggregate context is not the deterministic derivation")
    lock_sha = review_evidence["static_lock_sha256"]
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
        if record["assignment_id"] != record["run_id"]:
            raise ProtocolError("report launch assignment/slot/run identity drifted")
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
        or contract.get("contract_id") != "v5-evaluator-runtime-instantiation-v2"
        or contract.get("packet_authority")
        != "PROTOCOL_DERIVED_IMMUTABLE_AGGREGATION_STAGE"
        or contract.get("production_lease_route") != "ASSIGNMENT_ID_ONLY"
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
        packet = validate_consistency_packet(packet)
        if packet["mode"] != row["mode"]:
            raise ProtocolError("consistency packet mode does not match its assignment")
        return packet
    if role == "adjudicator":
        packet = validate_adjudication_packet(packet)
        if packet["mode"] != row["mode"]:
            raise ProtocolError("adjudication packet mode does not match its assignment")
        return packet
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
    expected_directories = {
        parent.as_posix()
        for path_text in expected_files
        for parent in PurePosixPath(path_text).parents
        if parent.as_posix() not in ("", ".")
    }
    actual_files: set[str] = set()
    actual_directories: set[str] = set()
    for path in input_root.rglob("*"):
        relative = path.relative_to(input_root).as_posix()
        if path.is_symlink() or not (path.is_dir() or path.is_file()):
            raise ProtocolError(f"evaluator input tree has an unsupported entry: {relative}")
        if path.is_file():
            actual_files.add(relative)
            if relative not in expected_files or path.read_bytes() != expected_files[relative]:
                raise ProtocolError(f"evaluator input file substitution: {relative}")
        else:
            actual_directories.add(relative)
    if actual_files != set(expected_files):
        raise ProtocolError("evaluator input file set is not exact")
    if actual_directories != expected_directories:
        raise ProtocolError("evaluator input directory set is not exact")


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
        if stage.exists() or stage.is_symlink():
            _discard_private_aggregation_stage(stage)


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
        if stage.exists() or stage.is_symlink():
            _discard_private_aggregation_stage(stage)


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


def verify_production_lease_workspace(
    lease: dict[str, Any],
    static_root: Path,
    *,
    report_byte_tree: Any | None = None,
) -> None:
    """Revalidate the exact launch-bound input workspace before trusting output."""

    launch = load_bound_launch(lease)
    workspace_root = Path(launch["workspace_root"])
    input_root = Path(launch["input_root"])
    output_root = Path(launch["output_root"])
    if (
        workspace_root.is_symlink()
        or not workspace_root.is_dir()
        or stat.S_IMODE(workspace_root.lstat().st_mode) != 0o500
        or input_root != workspace_root / "input"
        or output_root != workspace_root / "output"
        or input_root.is_symlink()
        or not input_root.is_dir()
        or stat.S_IMODE(input_root.lstat().st_mode) != 0o500
        or output_root.is_symlink()
        or not output_root.is_dir()
        or {path.name for path in workspace_root.iterdir()} != {"input", "output"}
    ):
        raise ProtocolError("lease-bound workspace topology drifted")
    for path in input_root.rglob("*"):
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            raise ProtocolError("lease-bound input contains an unsupported entry")
        expected_mode = 0o400 if path.is_file() else 0o500
        if stat.S_IMODE(path.lstat().st_mode) != expected_mode:
            raise ProtocolError(
                f"lease-bound input mode drifted: {path.relative_to(input_root)}"
            )
    packet_bytes = load_bound_input_packet_bytes(lease)
    if launch["role"] == "report":
        plan = validate_report_input_plan(
            strict_json_loads(packet_bytes, "lease report input plan"), launch
        )
        if report_byte_tree is None:
            report_byte_tree = run_trusted_module(
                "prepare.py", "v5_seal_report_input_byte_tree"
            )["byte_tree_v1"]
        verify_report_input_tree(
            input_root, static_root, plan, report_byte_tree
        )
    else:
        verify_evaluator_input_tree(
            input_root,
            static_root,
            {
                "input_packet_path": "packet.json",
                "schema_paths": launch["schema_paths"],
            },
            packet_bytes,
        )


def verify_production_lease_authority(
    lease: dict[str, Any],
    static_root: Path,
    *,
    ready_documents: dict[str, Any] | None = None,
) -> None:
    """Rederive one persisted lease from authenticated static/stage authority."""

    launch = load_bound_launch(lease)
    launch_bytes = load_bound_launch_bytes(lease)
    packet_bytes = load_bound_input_packet_bytes(lease)
    spec_bytes = load_bound_spec_bytes(lease)
    if ready_documents is None:
        ready_documents = load_ready_generated_documents(static_root)
    if launch["role"] == "report":
        run_id = launch["run_id"]
        expected_launch = next(
            (
                item
                for item in ready_documents["report-launch-records"]
                if item["run_id"] == run_id
            ),
            None,
        )
        launch_path = (
            static_root
            / "static"
            / "generated"
            / "launch-records"
            / f"{run_id}.json"
        )
        packet_path = (
            static_root
            / "static"
            / "generated"
            / "report-input-plans"
            / f"{run_id}.json"
        )
        spec_path = (
            static_root
            / "static"
            / "envelope-specs"
            / f"report-{launch['mode']}.json"
        )
        if expected_launch is None or launch != expected_launch:
            raise ProtocolError("persisted report lease is not the authenticated launch")
    else:
        packet_path, launch_path, spec_path, _packet, expected_launch = (
            load_authoritative_evaluator_material(
                static_root,
                launch["assignment_id"],
                capability=_PRODUCTION_LEASE_CAPABILITY,
                ready_documents=ready_documents,
            )
        )
        if launch != expected_launch:
            raise ProtocolError(
                "persisted evaluator lease is not the authoritative staged launch"
            )
    if (
        launch_bytes != launch_path.read_bytes()
        or packet_bytes != packet_path.read_bytes()
        or spec_bytes != spec_path.read_bytes()
    ):
        raise ProtocolError("persisted production lease material drifted from authority")


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
    if (
        type(spec["max_total_output_bytes"]) is not int
        or spec["max_total_output_bytes"] < 1
        or spec["max_total_output_bytes"] > MAX_ENVELOPE_CAPTURE_BYTES
    ):
        raise ProtocolError(
            "max_total_output_bytes must be within the trusted capture bound"
        )
    if not isinstance(spec["files"], list) or not spec["files"]:
        raise ProtocolError("envelope spec files must be a nonempty list")
    paths: list[str] = []
    for index, raw in enumerate(spec["files"]):
        item = require_exact_keys(raw, {"path", "required", "max_bytes", "utf8"}, f"envelope file {index}")
        path = require_relative_file(item["path"], f"envelope file {index} path")
        if path.startswith(ENCODED_OUTPUT_PATH_PREFIX):
            raise ProtocolError(
                f"envelope file {index} path uses the reserved encoded-output namespace"
            )
        paths.append(path)
        if type(item["required"]) is not bool or type(item["utf8"]) is not bool:
            raise ProtocolError(f"envelope file {index} flags must be booleans")
        if type(item["max_bytes"]) is not int or item["max_bytes"] < 0:
            raise ProtocolError(f"envelope file {index} max_bytes must be nonnegative")
        if item["max_bytes"] > spec["max_total_output_bytes"]:
            raise ProtocolError(
                f"envelope file {index} max_bytes exceeds the total capture bound"
            )
    if len(set(paths)) != len(paths):
        raise ProtocolError("envelope spec contains duplicate file paths")
    final = require_exact_keys(
        spec["final_response"],
        {"required", "max_bytes", "utf8", "utf8_fullmatch_regex"},
        "final response spec",
    )
    if type(final["required"]) is not bool or type(final["utf8"]) is not bool:
        raise ProtocolError("final response flags must be booleans")
    if (
        type(final["max_bytes"]) is not int
        or final["max_bytes"] < 0
        or final["max_bytes"] > MAX_ENVELOPE_CAPTURE_BYTES
    ):
        raise ProtocolError("final response max_bytes exceeds the trusted capture bound")
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


def load_bound_encoded_bytes(
    lease: dict[str, Any], bytes_field: str, digest_field: str, label: str
) -> bytes:
    try:
        data = base64.b64decode(lease[bytes_field], validate=True)
    except Exception as error:
        raise ProtocolError(f"lease {label} encoding is invalid") from error
    if sha256(data) != lease.get(digest_field):
        raise ProtocolError(f"lease {label} digest mismatch")
    return data


def load_bound_spec_bytes(lease: dict[str, Any]) -> bytes:
    return load_bound_encoded_bytes(
        lease,
        "envelope_spec_bytes_base64",
        "envelope_spec_sha256",
        "envelope spec",
    )


def load_bound_spec(lease: dict[str, Any]) -> dict[str, Any]:
    data = load_bound_spec_bytes(lease)
    value = strict_json_loads(data, "lease envelope spec")
    return validate_envelope_spec(value, require_ready=True)


def load_bound_launch_bytes(lease: dict[str, Any]) -> bytes:
    return load_bound_encoded_bytes(
        lease,
        "launch_record_bytes_base64",
        "launch_record_sha256",
        "launch record",
    )


def load_bound_launch(lease: dict[str, Any]) -> dict[str, Any]:
    data = load_bound_launch_bytes(lease)
    value = strict_json_loads(data, "lease launch record")
    launch = validate_launch_record(value)
    if launch["slot_id"] != lease.get("slot_id"):
        raise ProtocolError("lease/launch slot mismatch")
    return launch


def load_bound_input_packet(lease: dict[str, Any]) -> Any:
    return strict_json_loads(load_bound_input_packet_bytes(lease), "lease input packet")


def load_bound_input_packet_bytes(lease: dict[str, Any]) -> bytes:
    return load_bound_encoded_bytes(
        lease,
        "input_packet_bytes_base64",
        "input_packet_sha256",
        "input packet",
    )


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
    if not path_entry_exists(path):
        try:
            exclusive_write(path, expected)
        except FileExistsError:
            pass
        except BaseException:
            # The immutable hard-link CAS may have succeeded before a trailing
            # durability operation reported an error.  If it did not publish
            # anything, preserve that error.  Otherwise the exact committed
            # marker below dominates and is made durable again.
            if not path_entry_exists(path):
                raise
    if (
        not path.is_file()
        or path.is_symlink()
        or path.read_bytes() != expected
        or path.lstat().st_mode & 0o222
    ):
        raise ProtocolError(f"immutable ledger mismatch: {path}")
    fsync_directory(path.parent)


def _authoritative_leases(
    state_root: Path,
    *,
    production_reviewer_ids: frozenset[str] | None = None,
) -> list[dict[str, Any]]:
    slots_root = state_root / "slots"
    if not path_entry_exists(slots_root):
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
        launch = load_bound_launch(lease)
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
    production_context: tuple[Path, frozenset[str]] | None = None,
    production_capability: object | None = None,
) -> dict[str, Any]:
    if production_context is not None:
        if (
            production_capability is not _PRODUCTION_LEASE_CAPABILITY
            or static_root is not None
            or external_commitment_path is not None
            or test_capability is not None
        ):
            raise ProtocolError("private production lease context is invalid")
        verified_root, production_reviewer_ids = production_context
        state_root = Path(os.path.abspath(os.fspath(state_root)))
        if state_root != verified_root / "runtime" / "state":
            raise ProtocolError("production lease state root is not the verified bundle state")
    elif static_root is not None or external_commitment_path is not None:
        raise ProtocolError(
            "generic acquire_lease cannot initiate a production lease; "
            "use the assignment-only production wrapper"
        )
    else:
        state_root, verified_root, production_reviewer_ids = require_state_context(
            state_root,
            test_capability=test_capability,
        )
    agent_id = require_safe_id(agent_id, "agent ID")
    if verified_root is not None:
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
    if verified_root is not None:
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
        (
            expected_packet_path,
            expected_launch_path,
            expected_spec_path,
            _expected_packet,
            expected_launch,
        ) = load_authoritative_evaluator_material(
            verified_root,
            launch["assignment_id"],
            capability=_PRODUCTION_LEASE_CAPABILITY,
        )
        evaluator_row = evaluator_contract_index(
            load_ready_generated_documents(verified_root)
        )[launch["assignment_id"]]
        if (
            Path(os.path.abspath(os.fspath(launch_path))) != expected_launch_path
            or Path(os.path.abspath(os.fspath(input_packet_path)))
            != expected_packet_path
            or Path(os.path.abspath(os.fspath(spec_path))) != expected_spec_path
            or launch != expected_launch
            or launch_bytes != expected_launch_path.read_bytes()
            or input_packet_bytes != expected_packet_path.read_bytes()
        ):
            raise ProtocolError(
                "production evaluator lease must use its exact published stage artifacts"
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
    workspace_root = require_external_path(
        Path(launch["workspace_root"]), "launch workspace root"
    )
    if (
        input_root != workspace_root / "input"
        or attempt_root != workspace_root / "output"
    ):
        raise ProtocolError("launch input/output roots are not exact workspace children")
    workspace_parent = workspace_root.parent
    durable_mkdir(workspace_parent)
    if workspace_parent.is_symlink() or not workspace_parent.is_dir():
        raise ProtocolError("launch workspace parent is not a real directory")
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
        recover_exclusive_write_residues(state_root)
        terminal_aggregation_path = (
            state_root
            / "aggregation"
            / AGGREGATION_TERMINAL_FAILURE
        )
        if verified_root is not None and path_entry_exists(
            terminal_aggregation_path
        ):
            raise ProtocolError("aggregation has already terminated with an error")
        leases = _authoritative_leases(
            state_root, production_reviewer_ids=production_reviewer_ids
        )
        existing = next((item for item in leases if item["slot_id"] == slot_id), None)
        recovering = existing is not None
        if existing is not None:
            slot_root = state_root / "slots" / slot_id
            terminal_entries = {
                "terminal-claim.json",
                "canonical.json",
                "seal-failure.json",
            }
            if any(
                (slot_root / name).exists() or (slot_root / name).is_symlink()
                for name in terminal_entries
            ):
                raise LeaseAlreadyExists(
                    f"slot {slot_id} is already in a terminal state"
                )
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
            if path_entry_exists(agent_claim_path) or path_entry_exists(root_claim_path):
                raise ProtocolError("orphan uniqueness claim exists without an authoritative lease")
            if workspace_root.exists() or workspace_root.is_symlink():
                raise LeaseAlreadyExists(
                    "unclaimed launch workspace is not fresh"
                )
            if path_entry_exists(attempt_root):
                raise LeaseAlreadyExists("attempt root is not fresh")
            try:
                exclusive_write(lease_path, canonical_json_bytes(lease))
            except FileExistsError as error:
                raise LeaseAlreadyExists("slot lease CAS was lost") from error
            os.chmod(lease_path, 0o400)
            fsync_directory(lease_path.parent)
        maybe_inject_fault(fault_after, "lease-cas")
        failure_path = state_root / "slots" / slot_id / "lease-failure.json"
        if path_entry_exists(failure_path):
            raise ProtocolError("lease initialization has an immutable failure ledger")
        claim = {
            "schema_version": 1,
            "slot_id": slot_id,
            "agent_id": agent_id,
            "attempt_root": str(attempt_root),
            "launch_record_sha256": lease["launch_record_sha256"],
            "lease_sha256": sha256(canonical_json_bytes(lease)),
        }
        ready_path = state_root / "slots" / slot_id / "lease-ready.json"
        ready = {
            "schema_version": 1,
            "status": "LEASE-READY",
            "slot_id": slot_id,
            "attempt_id": lease["attempt_id"],
            "lease_sha256": sha256(canonical_json_bytes(lease)),
            "agent_claim_sha256": sha256(canonical_json_bytes(claim)),
            "attempt_root_claim_sha256": root_claim_id,
        }
        try:
            if not path_entry_exists(workspace_root):
                os.mkdir(workspace_root, mode=0o700)
            elif (
                not recovering
                or workspace_root.is_symlink()
                or not workspace_root.is_dir()
            ):
                raise ProtocolError("lease-bound workspace root is not recoverable")
            os.chmod(workspace_root, 0o700)
            if recovering:
                for path in sorted(
                    workspace_root.iterdir(), key=lambda item: item.name
                ):
                    if path.name.startswith(
                        (".input-stage-", ".evaluator-input-stage-")
                    ):
                        _discard_private_aggregation_stage(path)
            allowed_workspace_entries = {"input", "output"}
            unexpected_workspace_entries = {
                path.name for path in workspace_root.iterdir()
            } - allowed_workspace_entries
            if unexpected_workspace_entries:
                raise ProtocolError(
                    "lease workspace contains unexpected sibling entries: "
                    f"{sorted(unexpected_workspace_entries)}"
                )
            if launch["role"] == "report":
                if report_plan is None or verified_root is None:
                    raise ProtocolError(
                        "report input materialization lacks a verified production context"
                    )
                materialize_bound_report_inputs(
                    launch_path,
                    input_packet_path,
                    launch,
                    report_plan,
                    verified_root,
                )
            elif verified_root is not None:
                if evaluator_row is None:
                    raise ProtocolError(
                        "evaluator input materialization lacks its assignment contract"
                    )
                materialize_evaluator_input_tree(
                    input_root,
                    verified_root,
                    evaluator_row,
                    input_packet_bytes,
                )
            else:
                input_root.mkdir(parents=True, exist_ok=True)
                os.chmod(input_root, 0o500)
            if not path_entry_exists(attempt_root):
                os.mkdir(attempt_root, mode=0o700)
            elif not recovering or not attempt_root.is_dir() or attempt_root.is_symlink():
                raise ProtocolError("lease-bound attempt root is not recoverable")
            if recovering and not path_entry_exists(ready_path) and any(attempt_root.iterdir()):
                raise ProtocolError(
                    "pre-ready recovered attempt output root must be empty"
                )
            if {path.name for path in workspace_root.iterdir()} != {
                "input",
                "output",
            }:
                raise ProtocolError("ready workspace child inventory is not exact")
            os.chmod(attempt_root, 0o700)
            os.chmod(workspace_root, 0o500)
            fsync_directory(workspace_root)
            fsync_directory(workspace_parent)
            maybe_inject_fault(fault_after, "attempt-root")
            _write_or_validate_immutable(agent_claim_path, claim)
            maybe_inject_fault(fault_after, "agent-claim")
            _write_or_validate_immutable(root_claim_path, claim)
            maybe_inject_fault(fault_after, "root-claim")
            _write_or_validate_immutable(
                ready_path, ready
            )
            maybe_inject_fault(fault_after, "ready")
        except InjectedFault:
            raise
        except BaseException as error:
            if path_entry_exists(ready_path):
                # Once the exact ready marker is published it dominates a
                # trailing durability exception.  Revalidate every preceding
                # immutable claim and the exact workspace before returning
                # success; never create a contradictory failure marker.
                _write_or_validate_immutable(agent_claim_path, claim)
                _write_or_validate_immutable(root_claim_path, claim)
                _write_or_validate_immutable(ready_path, ready)
                if (
                    workspace_root.is_symlink()
                    or not workspace_root.is_dir()
                    or {path.name for path in workspace_root.iterdir()}
                    != {"input", "output"}
                    or input_root.is_symlink()
                    or not input_root.is_dir()
                    or attempt_root.is_symlink()
                    or not attempt_root.is_dir()
                    or stat.S_IMODE(workspace_root.lstat().st_mode) != 0o500
                    or stat.S_IMODE(attempt_root.lstat().st_mode) != 0o700
                ):
                    raise ProtocolError(
                        "published lease readiness marker has invalid workspace state"
                    ) from error
                if verified_root is not None:
                    verify_production_lease_workspace(lease, verified_root)
                return lease
            # Before readiness there is no terminal initialization outcome:
            # exact intermediate claims/workspace materialization are
            # idempotently recoverable by the same agent.  Persisting a
            # failure companion here could turn a post-publication exception
            # into contradictory state or make a transient error permanent.
            raise
    return lease


def scan_output(root: Path, max_capture_bytes: int) -> list[dict[str, Any]]:
    if (
        type(max_capture_bytes) is not int
        or max_capture_bytes < 1
        or max_capture_bytes > MAX_ENVELOPE_CAPTURE_BYTES
    ):
        raise ProtocolError("output capture byte bound is invalid")
    if not path_entry_exists(root):
        return []
    entries: list[dict[str, Any]] = []
    captured_bytes = 0
    captured_path_bytes = 0

    def identity(info: os.stat_result) -> tuple[int, int, int, int, int, int]:
        return (
            info.st_dev,
            info.st_ino,
            info.st_mode,
            info.st_size,
            info.st_mtime_ns,
            info.st_ctime_ns,
        )

    def stable_file_bytes(
        directory_fd: int,
        name: str,
        listed: os.stat_result,
        remaining_capture_bytes: int,
    ) -> tuple[bytes | None, int]:
        flags = (
            os.O_RDONLY
            | getattr(os, "O_NOFOLLOW", 0)
            | getattr(os, "O_NONBLOCK", 0)
        )
        original_mode = stat.S_IMODE(listed.st_mode)
        mode_adjusted = False
        try:
            fd = os.open(name, flags, dir_fd=directory_fd)
        except PermissionError:
            os.chmod(
                name,
                original_mode | stat.S_IRUSR,
                dir_fd=directory_fd,
                follow_symlinks=False,
            )
            adjusted = os.stat(
                name, dir_fd=directory_fd, follow_symlinks=False
            )
            if (
                (listed.st_dev, listed.st_ino, listed.st_size, listed.st_mtime_ns)
                != (
                    adjusted.st_dev,
                    adjusted.st_ino,
                    adjusted.st_size,
                    adjusted.st_mtime_ns,
                )
                or not stat.S_ISREG(adjusted.st_mode)
            ):
                raise ProtocolError(
                    "output file changed while restoring coordinator readability"
                )
            listed = adjusted
            mode_adjusted = True
            try:
                fd = os.open(name, flags, dir_fd=directory_fd)
            except BaseException:
                os.chmod(
                    name,
                    original_mode,
                    dir_fd=directory_fd,
                    follow_symlinks=False,
                )
                raise
        try:
            opened = os.fstat(fd)
            if identity(listed) != identity(opened) or not stat.S_ISREG(opened.st_mode):
                raise ProtocolError(f"output entry changed during stable open: {name}")
            after = os.fstat(fd)
            if identity(opened) != identity(after):
                raise ProtocolError(f"output file changed during capture: {name}")
            if opened.st_size > remaining_capture_bytes:
                return None, opened.st_size
            chunks: list[bytes] = []
            remaining = remaining_capture_bytes + 1
            while remaining:
                chunk = os.read(fd, min(1024 * 1024, remaining))
                if not chunk:
                    break
                chunks.append(chunk)
                remaining -= len(chunk)
            data = b"".join(chunks)
            after = os.fstat(fd)
            if (
                identity(opened) != identity(after)
                or len(data) != after.st_size
                or len(data) > remaining_capture_bytes
            ):
                raise ProtocolError(f"output file changed during bounded capture: {name}")
            return data, after.st_size
        finally:
            if mode_adjusted:
                os.fchmod(fd, original_mode)
            os.close(fd)

    directory_flags = (
        os.O_RDONLY
        | getattr(os, "O_DIRECTORY", 0)
        | getattr(os, "O_NOFOLLOW", 0)
    )
    try:
        root_listed = os.stat(root, follow_symlinks=False)
    except OSError as error:
        raise ProtocolError(
            "attempt output root is not a stable non-symlink directory"
        ) from error
    if not stat.S_ISDIR(root_listed.st_mode):
        raise ProtocolError(
            "attempt output root is not a stable non-symlink directory"
        )
    root_original_mode = stat.S_IMODE(root_listed.st_mode)
    root_mode_adjusted = False
    root_required_mode = root_original_mode | stat.S_IRUSR | stat.S_IXUSR
    if root_required_mode != root_original_mode:
        os.chmod(root, root_required_mode, follow_symlinks=False)
        root_adjusted = os.stat(root, follow_symlinks=False)
        if (
            (
                root_listed.st_dev,
                root_listed.st_ino,
                root_listed.st_size,
                root_listed.st_mtime_ns,
            )
            != (
                root_adjusted.st_dev,
                root_adjusted.st_ino,
                root_adjusted.st_size,
                root_adjusted.st_mtime_ns,
            )
            or not stat.S_ISDIR(root_adjusted.st_mode)
        ):
            raise ProtocolError(
                "attempt output root changed while restoring coordinator readability"
            )
        root_listed = root_adjusted
        root_mode_adjusted = True
    try:
        root_fd = os.open(root, directory_flags)
    except PermissionError:
        if root_mode_adjusted:
            os.chmod(root, root_original_mode, follow_symlinks=False)
        raise ProtocolError(
            "attempt output root is unreadable after coordinator mode recovery"
        )
    except OSError as error:
        if root_mode_adjusted:
            os.chmod(root, root_original_mode, follow_symlinks=False)
        raise ProtocolError(
            "attempt output root is not a stable non-symlink directory"
        ) from error
    directory_modes_to_restore: dict[tuple[str, ...], int] = {}
    open_relative_directory: Callable[[tuple[str, ...]], int] | None = None
    try:
        root_identity = identity(os.fstat(root_fd))
        directory_identities: dict[tuple[str, ...], tuple[int, int, int, int, int, int]] = {
            (): root_identity
        }

        def open_relative_directory(parts: tuple[str, ...]) -> int:
            descriptor = os.dup(root_fd)
            walked: tuple[str, ...] = ()
            try:
                for part in parts:
                    child = os.open(part, directory_flags, dir_fd=descriptor)
                    os.close(descriptor)
                    descriptor = child
                    walked = (*walked, part)
                    expected = directory_identities.get(walked)
                    if expected is None or identity(os.fstat(descriptor)) != expected:
                        raise ProtocolError(
                            "output directory changed during descriptor traversal"
                        )
                return descriptor
            except BaseException:
                os.close(descriptor)
                raise

        pending: list[tuple[str, ...]] = [()]
        visited: list[tuple[str, ...]] = []
        observed_entries = 0
        capture_limit_reason: str | None = None
        while pending:
            parts = pending.pop()
            try:
                directory_fd = open_relative_directory(parts)
            except OSError as error:
                raise ProtocolError(
                    "output directory disappeared during descriptor traversal"
                ) from error
            try:
                before = os.fstat(directory_fd)
                if (
                    not stat.S_ISDIR(before.st_mode)
                    or identity(before) != directory_identities[parts]
                ):
                    raise ProtocolError(
                        "output traversal descriptor is not the expected directory"
                    )
                current: list[os.DirEntry[str]] = []
                with os.scandir(directory_fd) as iterator:
                    for child in iterator:
                        observed_entries += 1
                        if observed_entries > MAX_OUTPUT_CAPTURE_ENTRIES:
                            capture_limit_reason = "entry-count"
                            break
                        current.append(child)
                if capture_limit_reason is None:
                    current.sort(key=lambda item: item.name)
                    for entry in current:
                        child_parts = (*parts, entry.name)
                        raw_relative = PurePosixPath(*child_parts).as_posix()
                        relative = encode_output_path_token(raw_relative)
                        relative_bytes = len(relative.encode("utf-8"))
                        if (
                            captured_path_bytes + relative_bytes
                            > MAX_OUTPUT_CAPTURE_PATH_BYTES
                        ):
                            capture_limit_reason = "path-bytes"
                            break
                        captured_path_bytes += relative_bytes
                        listed = os.stat(
                            entry.name,
                            dir_fd=directory_fd,
                            follow_symlinks=False,
                        )
                        if stat.S_ISLNK(listed.st_mode):
                            entries.append({"path": relative, "kind": "symlink"})
                        elif stat.S_ISDIR(listed.st_mode):
                            entries.append({"path": relative, "kind": "directory"})
                            original_mode = stat.S_IMODE(listed.st_mode)
                            required_mode = original_mode | stat.S_IRUSR | stat.S_IXUSR
                            if required_mode != original_mode:
                                os.chmod(
                                    entry.name,
                                    required_mode,
                                    dir_fd=directory_fd,
                                    follow_symlinks=False,
                                )
                                adjusted = os.stat(
                                    entry.name,
                                    dir_fd=directory_fd,
                                    follow_symlinks=False,
                                )
                                if (
                                    (
                                        listed.st_dev,
                                        listed.st_ino,
                                        listed.st_size,
                                        listed.st_mtime_ns,
                                    )
                                    != (
                                        adjusted.st_dev,
                                        adjusted.st_ino,
                                        adjusted.st_size,
                                        adjusted.st_mtime_ns,
                                    )
                                    or not stat.S_ISDIR(adjusted.st_mode)
                                ):
                                    raise ProtocolError(
                                        "output directory changed while restoring coordinator readability"
                                    )
                                directory_modes_to_restore[child_parts] = original_mode
                                listed = adjusted
                            directory_identities[child_parts] = identity(listed)
                            pending.append(child_parts)
                        elif stat.S_ISREG(listed.st_mode):
                            data, size = stable_file_bytes(
                                directory_fd,
                                entry.name,
                                listed,
                                max_capture_bytes - captured_bytes,
                            )
                            if data is not None:
                                captured_bytes += len(data)
                            entries.append(
                                {
                                    "path": relative,
                                    "kind": "file",
                                    "captured": data is not None,
                                    "size": size,
                                    "data": data,
                                }
                            )
                        else:
                            entries.append({"path": relative, "kind": "special"})
                if identity(before) != identity(os.fstat(directory_fd)):
                    raise ProtocolError(
                        "output directory changed during iterative traversal"
                    )
                visited.append(parts)
            finally:
                os.close(directory_fd)
            if capture_limit_reason is not None:
                pending.clear()
                break

        if capture_limit_reason is not None:
            entries = [
                {
                    "path": output_capture_limit_path(capture_limit_reason),
                    "kind": "capture-limit",
                }
            ]

        # Reopen each directory through the original root descriptor after the
        # full walk.  This preserves the former start/end identity guarantee
        # without Python recursion or one open descriptor per nesting level.
        for parts in visited:
            try:
                directory_fd = open_relative_directory(parts)
            except OSError as error:
                raise ProtocolError(
                    "output directory disappeared after iterative traversal"
                ) from error
            try:
                if identity(os.fstat(directory_fd)) != directory_identities[parts]:
                    raise ProtocolError(
                        "output directory changed after iterative traversal"
                    )
            finally:
                os.close(directory_fd)
        if identity(os.stat(root, follow_symlinks=False)) != root_identity:
            raise ProtocolError("attempt output root path changed during traversal")
    finally:
        if open_relative_directory is not None:
            for parts, original_mode in sorted(
                directory_modes_to_restore.items(),
                key=lambda item: len(item[0]),
                reverse=True,
            ):
                directory_fd = open_relative_directory(parts)
                try:
                    os.fchmod(directory_fd, original_mode)
                finally:
                    os.close(directory_fd)
        if root_mode_adjusted:
            os.fchmod(root_fd, root_original_mode)
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
            if packet["mode"] != launch["mode"]:
                raise ProtocolError(
                    "consistency packet mode does not match the bound launch"
                )
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
            packet = validate_adjudication_packet(input_packet)
            if packet["mode"] != launch["mode"]:
                raise ProtocolError(
                    "adjudication packet mode does not match the bound launch"
                )
            validate_adjudication(output, packet)
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
    final_response: bytes | OversizedFinalResponse | None,
    process_disposition: str,
    process_exit_code: int | None,
    metadata: dict[str, Any],
    *,
    fault_after: str | None = None,
) -> dict[str, Any]:
    violations: list[str] = []
    scanned = scan_output(attempt_root, MAX_ENVELOPE_CAPTURE_BYTES)
    retained_output_bytes = sum(
        len(item["data"])
        for item in scanned
        if item["kind"] == "file" and item["captured"]
    )
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
        _raw_path, portable_path = decode_output_path_token(path)
        record: dict[str, Any] = {
            "path": path,
            "kind": kind,
            "declared": portable_path
            and (
                path in declared
                or (kind == "directory" and path in declared_parent_directories)
            ),
        }
        if not portable_path:
            violations.append(f"invalid-path:{path}")
        if kind == "file":
            data = entry["data"]
            size = entry["size"]
            captured = entry["captured"]
            total_bytes += size
            record.update(
                {
                    "size": size,
                    "sha256": sha256(data) if captured else None,
                    "captured": captured,
                }
            )
            if captured:
                payload_relative = envelope_payload_relative_path(path)
                write_stage_file(
                    stage / "payload" / Path(*payload_relative.parts), data
                )
                maybe_inject_fault(fault_after, "envelope-capture")
            else:
                violations.append(f"uncaptured-oversize:{path}:{size}")
            if portable_path and path in declared:
                requirement = declared[path]
                if size > requirement["max_bytes"]:
                    violations.append(f"oversize:{path}:{size}:{requirement['max_bytes']}")
                if captured and requirement["utf8"]:
                    try:
                        data.decode("utf-8")
                    except UnicodeDecodeError:
                        violations.append(f"non-utf8:{path}")
            else:
                violations.append(f"unexpected:{path}")
        elif kind == "directory" and (
            not portable_path or path not in declared_parent_directories
        ):
            violations.append(f"unexpected-directory:{path}")
        elif kind in ("symlink", "special", "not-directory"):
            violations.append(f"{kind}:{path}")
        elif kind == "capture-limit":
            violations.append(output_capture_limit_violation(path))
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
    hard_capture_overflow = any(
        entry["kind"] == "capture-limit"
        or (entry["kind"] == "file" and not entry["captured"])
        for entry in scanned
    )
    final_spec = spec["final_response"]
    final_response_bytes, final_descriptor = describe_final_response(final_response)
    if not final_descriptor["present"]:
        final_record: dict[str, Any] = {"present": False}
        if final_spec["required"]:
            violations.append("missing:final-response")
    else:
        final_size = final_descriptor["size"]
        final_captured = (
            final_response_bytes is not None
            and final_size
            <= MAX_ENVELOPE_CAPTURE_BYTES - retained_output_bytes
        )
        final_record = {
            "present": True,
            "captured": final_captured,
            "size": final_size,
            "sha256": final_descriptor["sha256"],
            "prefix_sha256": final_descriptor["prefix_sha256"],
        }
        if final_captured:
            assert final_response_bytes is not None
            write_stage_file(
                stage / "payload" / "final-response.bin", final_response_bytes
            )
        else:
            hard_capture_overflow = True
            violations.append(
                f"uncaptured-oversize:final-response:{final_size}"
            )
        if final_size > final_spec["max_bytes"]:
            violations.append(
                f"oversize:final-response:{final_size}:{final_spec['max_bytes']}"
            )
        if final_captured:
            assert final_response_bytes is not None
            try:
                final_text = final_response_bytes.decode("utf-8")
            except UnicodeDecodeError:
                violations.append("non-utf8:final-response")
            else:
                if re.fullmatch(final_spec["utf8_fullmatch_regex"], final_text) is None:
                    violations.append("format:final-response")
    semantic_errors = (
        ["semantic:output-capture-hard-limit"]
        if hard_capture_overflow
        else semantic_output_errors(
            lease,
            (
                primary["data"]
                if primary is not None
                and primary["kind"] == "file"
                and primary["captured"]
                else None
            ),
        )
    )
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
            "final_response_size",
            "final_response_sha256",
            "final_response_prefix_sha256",
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
        or not valid_final_response_binding(
            terminal_claim["final_response_size"],
            terminal_claim["final_response_sha256"],
            terminal_claim["final_response_prefix_sha256"],
        )
        or not isinstance(terminal_claim["metadata_sha256"], str)
        or not HEX64.fullmatch(terminal_claim["metadata_sha256"])
        or terminal_claim["envelope_sha256"] != pointer["envelope_sha256"]
    ):
        raise ProtocolError("terminal claim identity/content binding is invalid")
    if (
        object_path.name != pointer["envelope_sha256"]
        or object_path.parent.name != "sha256"
        or object_path.parent.parent.name != "objects"
    ):
        raise ProtocolError("canonical object path/digest mismatch")
    object_chain = (
        object_path.parent.parent,
        object_path.parent,
        object_path,
    )
    object_chain_identities: list[tuple[int, int]] = []
    for component in object_chain:
        try:
            info = component.lstat()
        except OSError as error:
            raise ProtocolError(
                "canonical object chain is unavailable"
            ) from error
        if not stat.S_ISDIR(info.st_mode):
            raise ProtocolError(
                "canonical object chain contains a non-directory or symlink"
            )
        object_chain_identities.append((info.st_dev, info.st_ino))
    if byte_tree_digest(object_path) != pointer["envelope_sha256"]:
        raise ProtocolError("canonical object byte-tree digest mismatch")
    for component, expected_identity in zip(
        object_chain, object_chain_identities, strict=True
    ):
        try:
            info = component.lstat()
        except OSError as error:
            raise ProtocolError(
                "canonical object chain disappeared during verification"
            ) from error
        if (
            not stat.S_ISDIR(info.st_mode)
            or (info.st_dev, info.st_ino) != expected_identity
        ):
            raise ProtocolError(
                "canonical object chain changed during verification"
            )
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
    if (
        not isinstance(records, list)
        or len(records) > MAX_OUTPUT_CAPTURE_ENTRIES
    ):
        raise ProtocolError("envelope output entries must be a list")
    seen_paths: list[str] = []
    retained_path_bytes = 0
    total_bytes = 0
    retained_output_bytes = 0
    violations: list[str] = []
    hard_capture_overflow = False
    file_records: dict[str, dict[str, Any]] = {}
    file_payload_paths: dict[str, str] = {}
    for raw in records:
        if not isinstance(raw, dict):
            raise ProtocolError("envelope output record is not an object")
        kind = raw.get("kind")
        expected_keys = {
            "path",
            "kind",
            "declared",
            "size",
            "sha256",
            "captured",
        } if kind == "file" else {
            "path",
            "kind",
            "declared",
        }
        record = require_exact_keys(raw, expected_keys, "envelope output record")
        path = record["path"]
        _raw_path, portable_path = decode_output_path_token(path)
        retained_path_bytes += len(path.encode("utf-8"))
        if retained_path_bytes > MAX_OUTPUT_CAPTURE_PATH_BYTES:
            raise ProtocolError(
                "envelope output path tokens exceed the hard byte limit"
            )
        if kind not in (
            "file",
            "directory",
            "symlink",
            "special",
            "not-directory",
            "capture-limit",
        ):
            raise ProtocolError("envelope output record kind is invalid")
        expected_declared = portable_path and (
            path in declared
            or (kind == "directory" and path in declared_parent_directories)
        )
        if type(record["declared"]) is not bool or record["declared"] is not expected_declared:
            raise ProtocolError("envelope declared flag is not recomputable")
        seen_paths.append(path)
        if not portable_path:
            violations.append(f"invalid-path:{path}")
        if kind == "file":
            if (
                type(record["size"]) is not int
                or record["size"] < 0
                or type(record["captured"]) is not bool
            ):
                raise ProtocolError("envelope file record size/capture state is invalid")
            payload_relative = envelope_payload_relative_path(path)
            payload_path = object_path / "payload" / Path(*payload_relative.parts)
            data: bytes | None = None
            if record["captured"]:
                if (
                    not isinstance(record["sha256"], str)
                    or not HEX64.fullmatch(record["sha256"])
                    or not payload_path.is_file()
                    or payload_path.is_symlink()
                ):
                    raise ProtocolError(
                        f"captured envelope payload is missing or invalid: {path}"
                    )
                remaining_payload_bytes = (
                    MAX_ENVELOPE_CAPTURE_BYTES - retained_output_bytes
                )
                data = read_bounded_file_prefix(
                    payload_path,
                    remaining_payload_bytes,
                    f"captured envelope payload {path}",
                )
                if len(data) != record["size"] or sha256(data) != record["sha256"]:
                    raise ProtocolError(
                        f"envelope payload bytes disagree with record: {path}"
                    )
                retained_output_bytes += len(data)
                file_payload_paths[path] = payload_relative.as_posix()
            else:
                hard_capture_overflow = True
                if record["sha256"] is not None or path_entry_exists(payload_path):
                    raise ProtocolError(
                        f"uncaptured envelope file unexpectedly has payload bytes: {path}"
                    )
                violations.append(
                    f"uncaptured-oversize:{path}:{record['size']}"
                )
            total_bytes += record["size"]
            file_records[path] = record
            requirement = declared.get(path) if portable_path else None
            if requirement is None:
                violations.append(f"unexpected:{path}")
            else:
                if record["size"] > requirement["max_bytes"]:
                    violations.append(
                        f"oversize:{path}:{record['size']}:{requirement['max_bytes']}"
                    )
                if data is not None and requirement["utf8"]:
                    try:
                        data.decode("utf-8")
                    except UnicodeDecodeError:
                        violations.append(f"non-utf8:{path}")
        elif kind == "directory" and (
            not portable_path or path not in declared_parent_directories
        ):
            violations.append(f"unexpected-directory:{path}")
        elif kind in ("symlink", "special", "not-directory"):
            violations.append(f"{kind}:{path}")
        elif kind == "capture-limit":
            if len(records) != 1:
                raise ProtocolError(
                    "output capture-limit sentinel must be the only output record"
                )
            hard_capture_overflow = True
            violations.append(output_capture_limit_violation(path))
    if seen_paths != sorted(seen_paths) or len(seen_paths) != len(set(seen_paths)):
        raise ProtocolError("envelope output records are not unique and sorted")
    if len(set(file_payload_paths.values())) != len(file_payload_paths):
        raise ProtocolError("envelope output path encoding collided")
    payload_root = object_path / "payload"
    actual_payload_files: set[str] = set()
    if path_entry_exists(payload_root):
        for path in payload_root.rglob("*"):
            if path.is_symlink() or (not path.is_file() and not path.is_dir()):
                raise ProtocolError("canonical payload contains a non-regular entry")
            if path.is_file():
                relative_payload = path.relative_to(payload_root).as_posix()
                if relative_payload != "final-response.bin":
                    actual_payload_files.add(relative_payload)
    if actual_payload_files != set(file_payload_paths.values()):
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
    if retained_output_bytes > MAX_ENVELOPE_CAPTURE_BYTES:
        raise ProtocolError("retained output payload exceeds the hard byte limit")

    final_record = envelope["final_response"]
    if not isinstance(final_record, dict) or type(final_record.get("present")) is not bool:
        raise ProtocolError("envelope final-response record is invalid")
    final_path = object_path / "payload" / "final-response.bin"
    if final_record["present"]:
        require_exact_keys(
            final_record,
            {"present", "captured", "size", "sha256", "prefix_sha256"},
            "final response",
        )
        if (
            type(final_record["captured"]) is not bool
            or not valid_final_response_binding(
                final_record["size"],
                final_record["sha256"],
                final_record["prefix_sha256"],
            )
            or terminal_claim["final_response_size"] != final_record["size"]
            or terminal_claim["final_response_sha256"] != final_record["sha256"]
            or terminal_claim["final_response_prefix_sha256"]
            != final_record["prefix_sha256"]
        ):
            raise ProtocolError("final response record/terminal claim mismatch")
        final_bytes: bytes | None = None
        if final_record["captured"]:
            if (
                final_record["size"]
                > MAX_ENVELOPE_CAPTURE_BYTES - retained_output_bytes
            ):
                raise ProtocolError(
                    "captured final response exceeds the aggregate hard byte limit"
                )
            if not final_path.is_file() or final_path.is_symlink():
                raise ProtocolError("captured final response lacks regular payload bytes")
            final_bytes = read_bounded_file_prefix(
                final_path,
                MAX_ENVELOPE_CAPTURE_BYTES - retained_output_bytes,
                "captured final-response payload",
            )
            if (
                final_record["size"] != len(final_bytes)
                or final_record["sha256"] != sha256(final_bytes)
            ):
                raise ProtocolError("final response payload/digest mismatch")
        else:
            hard_capture_overflow = True
            if (
                path_entry_exists(final_path)
                or final_record["size"]
                <= MAX_ENVELOPE_CAPTURE_BYTES - retained_output_bytes
            ):
                raise ProtocolError("uncaptured final response state is invalid")
            violations.append(
                f"uncaptured-oversize:final-response:{final_record['size']}"
            )
        if final_record["size"] > spec["final_response"]["max_bytes"]:
            violations.append(
                f"oversize:final-response:{final_record['size']}:{spec['final_response']['max_bytes']}"
            )
        if final_bytes is not None:
            try:
                final_text = final_bytes.decode("utf-8")
            except UnicodeDecodeError:
                violations.append("non-utf8:final-response")
            else:
                if re.fullmatch(spec["final_response"]["utf8_fullmatch_regex"], final_text) is None:
                    violations.append("format:final-response")
    else:
        require_exact_keys(final_record, {"present"}, "absent final response")
        if (
            path_entry_exists(final_path)
            or terminal_claim["final_response_size"] is not None
            or terminal_claim["final_response_sha256"] is not None
            or terminal_claim["final_response_prefix_sha256"] is not None
        ):
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
    if primary_record is not None and primary_record["captured"]:
        primary_relative = envelope_payload_relative_path(launch["output_path"])
        primary_bytes = (
            object_path / "payload" / Path(*primary_relative.parts)
        ).read_bytes()
    expected_semantic_errors = (
        ["semantic:output-capture-hard-limit"]
        if hard_capture_overflow
        else semantic_output_errors(lease, primary_bytes)
    )
    if (
        envelope["semantic_errors"] != expected_semantic_errors
        or type(envelope["semantic_valid"]) is not bool
        or envelope["semantic_valid"] is not (not expected_semantic_errors)
        or pointer["semantic_valid"] is not envelope["semantic_valid"]
    ):
        raise ProtocolError("envelope semantic result disagrees with recomputation")
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
            "final_response_size",
            "final_response_sha256",
            "final_response_prefix_sha256",
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
        or not valid_final_response_binding(
            claim["final_response_size"],
            claim["final_response_sha256"],
            claim["final_response_prefix_sha256"],
        )
        or not isinstance(claim["process_disposition"], str)
        or SAFE_ID.fullmatch(claim["process_disposition"]) is None
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


def validate_committed_seal_failure(
    path: Path,
    lease: dict[str, Any],
    terminal_claim: dict[str, Any],
) -> dict[str, Any]:
    failure = require_exact_keys(
        read_committed_json(path, "seal failure"),
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
        or failure["slot_id"] != lease["slot_id"]
        or failure["attempt_id"] != lease["attempt_id"]
        or failure["terminal_claim_sha256"]
        != sha256(canonical_json_bytes(terminal_claim))
        or not isinstance(failure["error_type"], str)
        or SAFE_ID.fullmatch(failure["error_type"]) is None
        or path.read_bytes() != canonical_json_bytes(failure)
    ):
        raise ProtocolError("seal-failure ledger is not exactly claim-bound")
    return failure


def seal_attempt(
    state_root: Path,
    slot_id: str,
    lease_token: str,
    agent_id: str,
    attempt_root: Path,
    final_response: bytes | OversizedFinalResponse | None,
    process_disposition: str,
    process_exit_code: int | None,
    metadata: dict[str, Any],
    *,
    fault_after: str | None = None,
    static_root: Path | None = None,
    external_commitment_path: Path | None = None,
    test_capability: object | None = None,
    production_context: tuple[Path, frozenset[str]] | None = None,
    production_capability: object | None = None,
) -> dict[str, Any]:
    if production_context is not None:
        if (
            production_capability is not _PRODUCTION_LEASE_CAPABILITY
            or static_root is not None
            or external_commitment_path is not None
            or test_capability is not None
        ):
            raise ProtocolError("private production seal context is invalid")
        verified_root, production_reviewer_ids = production_context
        state_root = Path(os.path.abspath(os.fspath(state_root)))
        if state_root != verified_root / "runtime" / "state":
            raise ProtocolError("production seal state root is not the verified bundle state")
    elif static_root is not None or external_commitment_path is not None:
        raise ProtocolError(
            "generic seal_attempt cannot finalize a production lease; "
            "use the production seal wrapper"
        )
    else:
        state_root, _verified_root, production_reviewer_ids = require_state_context(
            state_root,
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
    process_disposition = require_safe_id(
        process_disposition, "process disposition"
    )
    if process_exit_code is not None and type(process_exit_code) is not int:
        raise ProtocolError("process exit code must be an integer or null")
    _final_response_bytes, final_response_descriptor = describe_final_response(
        final_response
    )
    # Validate the complete caller-authored terminal request before acquiring
    # the state lock or touching any recovery residue.  A request that could
    # not survive validate_terminal_claim must never publish a claim/pointer.
    metadata_bytes = canonical_json_bytes(metadata)
    lease_path = state_root / "slots" / slot_id / "lease.json"
    canonical_path = state_root / "slots" / slot_id / "canonical.json"
    terminal_claim_path = state_root / "slots" / slot_id / "terminal-claim.json"
    seal_failure_path = state_root / "slots" / slot_id / "seal-failure.json"
    with operation_lock(state_root):
        recover_exclusive_write_residues(state_root)
        canonical_preexisting = path_entry_exists(canonical_path)
        aggregation_terminal_path = (
            state_root
            / "aggregation"
            / AGGREGATION_TERMINAL_FAILURE
        )
        if (
            production_context is not None
            and not canonical_preexisting
            and path_entry_exists(aggregation_terminal_path)
        ):
            raise ProtocolError("aggregation has already terminated with an error")
        _authoritative_leases(
            state_root, production_reviewer_ids=production_reviewer_ids
        )
        if not lease_path.is_file():
            raise ProtocolError(f"slot {slot_id} has no started lease")
        lease = validate_lease(read_json(lease_path))
        launch = load_bound_launch(lease)
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
        if production_context is not None:
            verify_production_lease_authority(lease, verified_root)
        seal_request = {
            "lease_sha256": sha256(canonical_json_bytes(lease)),
            "final_response_size": final_response_descriptor["size"],
            "final_response_sha256": final_response_descriptor["sha256"],
            "final_response_prefix_sha256": final_response_descriptor[
                "prefix_sha256"
            ],
            "process_disposition": process_disposition,
            "process_exit_code": process_exit_code,
            "metadata_sha256": sha256(metadata_bytes),
        }
        expected_terminal_fields = {
            "schema_version": 1,
            "status": "TERMINAL-CLAIMED",
            "slot_id": slot_id,
            "attempt_id": lease["attempt_id"],
            "agent_id": agent_id,
            "attempt_root": lease["attempt_root"],
            **seal_request,
        }
        if canonical_preexisting:
            if path_entry_exists(seal_failure_path):
                raise TerminalAlreadyClaimed(
                    f"slot {slot_id} has both canonical and failed terminal state"
                )
            terminal_claim = validate_terminal_claim(
                read_committed_json(terminal_claim_path, "terminal claim"), lease
            )
            if any(
                terminal_claim.get(key) != value
                for key, value in expected_terminal_fields.items()
            ):
                raise TerminalAlreadyClaimed(
                    f"slot {slot_id} terminal recovery arguments do not match the claim"
                )
            pointer = read_committed_json(canonical_path, "canonical pointer")
            object_path = (
                state_root
                / "objects"
                / "sha256"
                / terminal_claim["envelope_sha256"]
            )
            semantic_verify_envelope(
                object_path, lease, pointer, terminal_claim
            )
            fsync_directory(object_path.parent)
            os.chmod(canonical_path, 0o400)
            os.chmod(canonical_path.parent, 0o500)
            fsync_directory(canonical_path.parent)
            fsync_directory(canonical_path.parent.parent)
            return pointer
        if production_context is not None:
            verify_production_lease_workspace(lease, verified_root)
        objects = state_root / "objects" / "sha256"
        durable_mkdir(objects)
        request_id = sha256(canonical_json_bytes(seal_request))[:24]
        stage = objects / f".stage-{lease['attempt_id']}-{request_id}"
        stage_prefix = f".stage-{lease['attempt_id']}-"
        terminal_claim: dict[str, Any]
        manifest: dict[str, Any]
        try:
            if path_entry_exists(terminal_claim_path):
                terminal_claim = validate_terminal_claim(
                    read_committed_json(terminal_claim_path, "terminal claim"),
                    lease,
                )
                if path_entry_exists(seal_failure_path):
                    validate_committed_seal_failure(
                        seal_failure_path, lease, terminal_claim
                    )
                    fsync_directory(seal_failure_path.parent)
                    raise TerminalAlreadyClaimed(
                        f"slot {slot_id} has an immutable failed terminal transition"
                    )
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
                # The claimed request owns its recovery stage.  Validate the
                # persisted claim against this retry before discarding any
                # sibling residue; a mismatched retry must be observationally
                # read-only so the original claimant can still recover.
                for residue in sorted(objects.iterdir(), key=lambda path: path.name):
                    if residue.name.startswith(stage_prefix) and residue != stage:
                        _discard_private_aggregation_stage(residue)
            else:
                if path_entry_exists(seal_failure_path):
                    raise ProtocolError("seal-failure ledger exists without terminal claim")
                for residue in sorted(objects.iterdir(), key=lambda path: path.name):
                    if residue.name.startswith(stage_prefix):
                        _discard_private_aggregation_stage(residue)
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
                    fault_after=fault_after,
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
                    "final_response_size": final_response_descriptor["size"],
                    "final_response_sha256": final_response_descriptor["sha256"],
                    "final_response_prefix_sha256": final_response_descriptor[
                        "prefix_sha256"
                    ],
                    "process_disposition": process_disposition,
                    "process_exit_code": process_exit_code,
                    "metadata_sha256": sha256(metadata_bytes),
                    "envelope_sha256": digest,
                }
                _write_or_validate_immutable(terminal_claim_path, terminal_claim)
            maybe_inject_fault(fault_after, "terminal-claim")
            object_path = objects / digest
            if path_entry_exists(object_path):
                if (
                    not object_path.is_dir()
                    or object_path.is_symlink()
                    or byte_tree_digest(object_path) != digest
                ):
                    raise ProtocolError(f"pre-existing envelope object is invalid: {digest}")
                fsync_directory(objects)
            else:
                if (
                    not stage.is_dir()
                    or stage.is_symlink()
                    or byte_tree_digest(stage) != digest
                ):
                    raise ProtocolError("terminal claim lacks its immutable recovery stage")
                try:
                    os.rename(stage, object_path)
                    fsync_directory(objects)
                except BaseException:
                    if (
                        not object_path.is_dir()
                        or object_path.is_symlink()
                        or byte_tree_digest(object_path) != digest
                    ):
                        raise
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
                _write_or_validate_immutable(canonical_path, pointer)
            except FileExistsError as error:  # pragma: no cover - helper normalizes races.
                raise CanonicalAlreadySealed(f"slot {slot_id} lost the first-terminal CAS") from error
            maybe_inject_fault(fault_after, "canonical-cas")
        except (InjectedFault, TerminalAlreadyClaimed):
            raise
        except BaseException as error:
            if path_entry_exists(canonical_path):
                # A successfully published canonical pointer dominates a
                # trailing durability exception.  Authenticate the complete
                # claim/object/pointer closure and finish hardening instead of
                # publishing a contradictory seal-failure ledger.
                committed_claim = validate_terminal_claim(
                    read_committed_json(terminal_claim_path, "terminal claim"),
                    lease,
                )
                if any(
                    committed_claim.get(key) != value
                    for key, value in expected_terminal_fields.items()
                ):
                    raise ProtocolError(
                        "published canonical pointer has a mismatched terminal claim"
                    ) from error
                committed_pointer = read_committed_json(
                    canonical_path, "canonical pointer"
                )
                committed_object = (
                    state_root
                    / "objects"
                    / "sha256"
                    / committed_claim["envelope_sha256"]
                )
                semantic_verify_envelope(
                    committed_object,
                    lease,
                    committed_pointer,
                    committed_claim,
                )
                fsync_directory(committed_object.parent)
                os.chmod(canonical_path, 0o400)
                os.chmod(canonical_path.parent, 0o500)
                fsync_directory(canonical_path.parent)
                fsync_directory(canonical_path.parent.parent)
                return committed_pointer
            if not path_entry_exists(terminal_claim_path):
                raise
            claimed = validate_terminal_claim(
                read_committed_json(terminal_claim_path, "terminal claim"), lease
            )
            if any(
                claimed.get(key) != value
                for key, value in expected_terminal_fields.items()
            ):
                raise ProtocolError(
                    "published terminal claim does not match its sealing request"
                ) from error
            claimed_digest = claimed["envelope_sha256"]
            published_object = state_root / "objects" / "sha256" / claimed_digest
            recovery_candidate = (
                published_object
                if path_entry_exists(published_object)
                else stage
            )
            recoverable = False
            if (
                recovery_candidate.is_dir()
                and not recovery_candidate.is_symlink()
                and byte_tree_digest(recovery_candidate) == claimed_digest
            ):
                try:
                    recovery_manifest = read_json(
                        recovery_candidate / "envelope.json"
                    )
                    recovery_pointer = {
                        "schema_version": 1,
                        "slot_id": slot_id,
                        "attempt_id": lease["attempt_id"],
                        "agent_id": agent_id,
                        "lease_sha256": sha256(canonical_json_bytes(lease)),
                        "launch_record_sha256": lease["launch_record_sha256"],
                        "terminal_claim_sha256": sha256(
                            canonical_json_bytes(claimed)
                        ),
                        "envelope_sha256": claimed_digest,
                        "format_valid": recovery_manifest["format_valid"],
                        "semantic_valid": recovery_manifest["semantic_valid"],
                    }
                    if recovery_candidate == published_object:
                        semantic_verify_envelope(
                            recovery_candidate,
                            lease,
                            recovery_pointer,
                            claimed,
                        )
                    elif (
                        type(recovery_manifest.get("format_valid")) is not bool
                        or type(recovery_manifest.get("semantic_valid")) is not bool
                    ):
                        raise ProtocolError(
                            "private recovery envelope lacks terminal validity fields"
                        )
                    recoverable = True
                except BaseException:
                    recoverable = False
            if recoverable:
                # The exact request still has a complete private or published
                # recovery object.  Leave it retryable and preserve the
                # triggering exception; do not turn a transient error into an
                # immutable failed terminal transition.
                raise
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
    if not path_entry_exists(root):
        return
    if not root.is_dir() or root.is_symlink():
        raise ProtocolError(f"{label} claim root is not a regular directory")
    actual: list[Path] = []
    if nested:
        expected_directories = {path.parent for path in expected}
        for directory in sorted(root.iterdir(), key=lambda item: item.name):
            if not directory.is_dir() or directory.is_symlink():
                raise ProtocolError(f"{label} claim root contains a non-directory entry")
            require_safe_id(directory.name, f"{label} claim directory")
            if directory not in expected_directories:
                raise ProtocolError(
                    f"{label} claim root contains an unreferenced directory"
                )
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
    if static_root is not None or external_commitment_path is not None:
        raise ProtocolError(
            "generic verify_state cannot verify production state; "
            "use verify_production_state"
        )
    state_root, _verified_root, production_reviewer_ids = require_state_context(
        state_root,
        test_capability=test_capability,
    )
    if not path_entry_exists(state_root):
        return {
            "schema_version": 1,
            "state_valid": True,
            "complete": False,
            "outcome": "IN_PROGRESS",
            "all_started_attempts_terminal": False,
            "all_outputs_valid": False,
            "staging_entries": [],
            "slots": [],
        }
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
    production_static_root: Path | None = None,
) -> dict[str, Any]:
    if (production_static_root is None) is not (
        production_reviewer_ids is None
    ):
        raise ProtocolError("production state verification context is incomplete")
    report_byte_tree = (
        run_trusted_module("prepare.py", "v5_state_report_input_byte_tree")[
            "byte_tree_v1"
        ]
        if production_static_root is not None
        else None
    )
    ready_documents: dict[str, Any] | None = None
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
    lock_path = state_root / ".protocol.lock"
    if (
        not lock_path.is_file()
        or lock_path.is_symlink()
        or not stat.S_ISREG(lock_path.lstat().st_mode)
    ):
        raise ProtocolError("protocol lock ledger is not a regular file")
    aggregation_root = state_root / "aggregation"
    committed_aggregation_stages: tuple[str, ...] = ()
    aggregation_claim: dict[str, Any] | None = None
    aggregation_stage_manifests: list[dict[str, Any]] = []
    aggregation_terminal: dict[str, Any] | None = None
    if path_entry_exists(aggregation_root):
        if not aggregation_root.is_dir() or aggregation_root.is_symlink():
            raise ProtocolError("aggregation state root is not a regular directory")
        allowed_aggregation_names = {
            AGGREGATION_COORDINATOR_CLAIM,
            AGGREGATION_TERMINAL_FAILURE,
            "derived",
            "final",
        }
        unexpected_aggregation = {
            path.name for path in aggregation_root.iterdir()
        } - allowed_aggregation_names
        if unexpected_aggregation:
            raise ProtocolError(
                "unexpected aggregation state entries: "
                f"{sorted(unexpected_aggregation)}"
            )
        committed_aggregation_stages = validate_aggregation_directory_inventory(
            aggregation_root, require_final=False
        )
        claim_path = aggregation_root / AGGREGATION_COORDINATOR_CLAIM
        claim = require_exact_keys(
            read_committed_json(claim_path, "aggregation coordinator claim"),
            {
                "schema_version",
                "status",
                "coordinator_actor_id",
                "static_lock_sha256",
            },
            "aggregation coordinator claim",
        )
        expected_static_lock_sha256 = (
            sha256((production_static_root / "STATIC-LOCK.json").read_bytes())
            if production_static_root is not None
            else None
        )
        if (
            claim["schema_version"] != 1
            or claim["status"] != "CLAIMED"
            or not isinstance(claim["coordinator_actor_id"], str)
            or PRODUCTION_ACTOR_ID.fullmatch(claim["coordinator_actor_id"]) is None
            or not isinstance(claim["static_lock_sha256"], str)
            or HEX64.fullmatch(claim["static_lock_sha256"]) is None
            or (
                expected_static_lock_sha256 is not None
                and claim["static_lock_sha256"] != expected_static_lock_sha256
            )
            or claim_path.read_bytes() != canonical_json_bytes(claim)
        ):
            raise ProtocolError("aggregation coordinator claim is malformed")
        aggregation_claim = claim
        aggregation_stage_manifests = validate_aggregation_stage_chain(
            aggregation_root, committed_aggregation_stages, claim
        )
        terminal_path = aggregation_root / AGGREGATION_TERMINAL_FAILURE
        if path_entry_exists(terminal_path):
            aggregation_terminal = validate_aggregation_terminal_failure(
                read_committed_json(
                    terminal_path, "aggregation terminal failure"
                )
            )
            if (
                aggregation_terminal["static_lock_sha256"]
                != claim["static_lock_sha256"]
                or aggregation_terminal["coordinator_actor_id"]
                != claim["coordinator_actor_id"]
                or terminal_path.read_bytes()
                != canonical_json_bytes(aggregation_terminal)
            ):
                raise ProtocolError(
                    "aggregation terminal failure is not bound to the coordinator claim"
                )
        for path in aggregation_root.rglob("*"):
            if path.is_symlink() or not (path.is_dir() or path.is_file()):
                raise ProtocolError(f"unsupported aggregation state entry: {path}")
    slots_root = state_root / "slots"
    results: list[dict[str, Any]] = []
    if path_entry_exists(slots_root) and (
        not slots_root.is_dir() or slots_root.is_symlink()
    ):
        raise ProtocolError("slots ledger root is not a regular directory")
    expected_agent_claims: dict[Path, dict[str, Any]] = {}
    expected_root_claims: dict[Path, dict[str, Any]] = {}
    referenced_objects: set[str] = set()
    slot_paths = (
        sorted(slots_root.iterdir(), key=lambda path: path.name)
        if path_entry_exists(slots_root)
        else []
    )
    if committed_aggregation_stages and not slot_paths:
        raise ProtocolError(
            "committed aggregation stages exist without authoritative attempt slots"
        )
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
        launch = load_bound_launch(lease)
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
        if path_entry_exists(lease_failure_path):
            failure = require_exact_keys(
                read_committed_json(lease_failure_path, "lease failure"),
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
            if path_entry_exists(ready_path):
                raise ProtocolError(f"slot {slot_id} has both ready and failed lease ledgers")
            results.append(
                {"slot_id": slot_id, "status": "LEASE_FAILED", "format_valid": False, "semantic_valid": False}
            )
            continue
        if not path_entry_exists(ready_path):
            results.append(
                {"slot_id": slot_id, "status": "LEASE_INITIALIZING", "format_valid": False, "semantic_valid": False}
            )
            continue
        ready = require_exact_keys(
            read_committed_json(ready_path, "lease readiness ledger"),
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
        if production_static_root is not None:
            if ready_documents is None:
                ready_documents = load_ready_generated_documents(
                    production_static_root
                )
            verify_production_lease_authority(
                lease,
                production_static_root,
                ready_documents=ready_documents,
            )
        if not path_entry_exists(terminal_path):
            if path_entry_exists(canonical_path) or path_entry_exists(failure_path):
                raise ProtocolError(f"slot {slot_id} has terminal artifacts without a claim")
            if production_static_root is not None:
                verify_production_lease_workspace(
                    lease,
                    production_static_root,
                    report_byte_tree=report_byte_tree,
                )
            results.append(
                {"slot_id": slot_id, "status": "STARTED", "format_valid": False, "semantic_valid": False}
            )
            continue
        if not terminal_path.is_file() or terminal_path.is_symlink() or terminal_path.lstat().st_mode & 0o222:
            raise ProtocolError(f"slot {slot_id} terminal claim is not immutable/regular")
        terminal_claim = validate_terminal_claim(read_json(terminal_path), lease)
        referenced_objects.add(terminal_claim["envelope_sha256"])
        if not path_entry_exists(canonical_path):
            if path_entry_exists(failure_path):
                validate_committed_seal_failure(
                    failure_path, lease, terminal_claim
                )
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
        if path_entry_exists(failure_path):
            raise ProtocolError(f"slot {slot_id} has both canonical and failed-seal ledgers")
        pointer = read_committed_json(canonical_path, "canonical pointer")
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
        primary_relative = envelope_payload_relative_path(launch["output_path"])
        primary_path = object_path / "payload" / Path(*primary_relative.parts)
        results.append(
            {
                "slot_id": slot_id,
                "status": "SEALED",
                "role": launch["role"],
                "envelope_sha256": digest,
                "primary_output_present": primary_path.is_file()
                and not primary_path.is_symlink(),
                "format_valid": envelope["format_valid"],
                "semantic_valid": envelope["semantic_valid"],
            }
        )
    if aggregation_claim is not None:
        validate_aggregation_attempt_bindings(
            committed_aggregation_stages,
            aggregation_stage_manifests,
            results,
            aggregation_terminal,
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
    objects_parent = state_root / "objects"
    objects_root = objects_parent / "sha256"
    staging_entries: list[str] = []
    if path_entry_exists(objects_parent):
        if not objects_parent.is_dir() or objects_parent.is_symlink():
            raise ProtocolError("content-addressed objects parent is not a regular directory")
        if {path.name for path in objects_parent.iterdir()} != {"sha256"}:
            raise ProtocolError(
                "content-addressed objects parent does not contain exactly sha256"
            )
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
    all_started_attempts_terminal = bool(results) and all(
        item["status"] == "SEALED" for item in results
    )
    final_published = bool(
        committed_aggregation_stages
        and committed_aggregation_stages[-1] == "final"
    )
    complete = final_published or aggregation_terminal is not None
    state_valid = not staging_entries and all(
        item["status"] in ("STARTED", "SEALED") for item in results
    )
    all_outputs_valid = all_started_attempts_terminal and all(
        item["format_valid"] and item["semantic_valid"] for item in results
    )
    return {
        "schema_version": 1,
        "state_valid": state_valid,
        "complete": complete,
        "outcome": (
            "ERROR"
            if aggregation_terminal is not None
            else "SUCCESS" if final_published else "IN_PROGRESS"
        ),
        "all_started_attempts_terminal": all_started_attempts_terminal,
        "all_outputs_valid": all_outputs_valid,
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


def validate_authenticated_review_evidence(
    value: Any, reviewer_ids: frozenset[str]
) -> dict[str, Any]:
    evidence = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "algorithm",
            "bundle_kind",
            "static_lock_sha256",
            "source_review_receipts",
            "snapshot_review_receipts",
        },
        "authenticated review evidence",
    )
    if (
        evidence["schema_version"] != 1
        or evidence["status"] != "AUTHENTICATED"
        or evidence["algorithm"] != AUTHENTICATED_REVIEW_EVIDENCE_ALGORITHM
        or evidence["bundle_kind"] != "PRODUCTION"
        or not isinstance(evidence["static_lock_sha256"], str)
        or not HEX64.fullmatch(evidence["static_lock_sha256"])
    ):
        raise ProtocolError("authenticated review evidence identity/status is invalid")
    source_records = evidence["source_review_receipts"]
    snapshot_records = evidence["snapshot_review_receipts"]
    if not isinstance(source_records, list) or not isinstance(snapshot_records, list):
        raise ProtocolError("authenticated review evidence inventories must be lists")
    if [record.get("name") if isinstance(record, dict) else None for record in source_records] != list(
        SOURCE_REVIEW_KINDS
    ):
        raise ProtocolError("authenticated source-review receipt order is not exact")
    if [
        record.get("hook_id") if isinstance(record, dict) else None
        for record in snapshot_records
    ] != list(SNAPSHOT_REVIEW_HOOK_IDS):
        raise ProtocolError("authenticated snapshot-review receipt order is not exact")
    observed_actor_ids: list[str] = []
    for index, raw in enumerate(source_records):
        record = require_exact_keys(
            raw, {"name", "receipt_sha256", "receipt"}, f"source review evidence {index}"
        )
        receipt = record["receipt"]
        if not isinstance(receipt, dict):
            raise ProtocolError("authenticated source-review receipt is not an object")
        if (
            not isinstance(record["receipt_sha256"], str)
            or not HEX64.fullmatch(record["receipt_sha256"])
        ):
            raise ProtocolError(f"source review evidence {index} digest is invalid")
        if sha256(canonical_json_bytes(receipt)) != record["receipt_sha256"]:
            raise ProtocolError("authenticated source-review receipt digest is not recomputable")
        expected_kind = SOURCE_REVIEW_KINDS[record["name"]]
        actor = receipt.get("actor")
        if (
            receipt.get("status") != "PASS"
            or receipt.get("review_kind") != expected_kind
            or not isinstance(actor, dict)
        ):
            raise ProtocolError("authenticated source-review receipt identity is invalid")
        observed_actor_ids.append(
            require_production_actor_id(
                actor.get("identity"), f"source reviewer evidence actor {index}"
            )
        )
    for index, raw in enumerate(snapshot_records):
        record = require_exact_keys(
            raw,
            {"hook_id", "receipt_sha256", "receipt"},
            f"snapshot review evidence {index}",
        )
        receipt = record["receipt"]
        if not isinstance(receipt, dict):
            raise ProtocolError("authenticated snapshot-review receipt is not an object")
        if (
            not isinstance(record["receipt_sha256"], str)
            or not HEX64.fullmatch(record["receipt_sha256"])
        ):
            raise ProtocolError(f"snapshot review evidence {index} digest is invalid")
        if sha256(canonical_json_bytes(receipt)) != record["receipt_sha256"]:
            raise ProtocolError("authenticated snapshot-review receipt digest is not recomputable")
        actor = receipt.get("actor")
        if (
            receipt.get("status") != "PASS"
            or receipt.get("phase") != "SNAPSHOT_REVIEW"
            or receipt.get("hook_id") != record["hook_id"]
            or not isinstance(actor, dict)
        ):
            raise ProtocolError("authenticated snapshot-review receipt identity is invalid")
        observed_actor_ids.append(
            require_production_actor_id(
                actor.get("identity"), f"snapshot reviewer evidence actor {index}"
            )
        )
    if len(observed_actor_ids) != 11 or frozenset(observed_actor_ids) != reviewer_ids:
        raise ProtocolError(
            "authenticated review evidence actors do not equal the locked reviewer exclusions"
        )
    return strict_json_loads(
        canonical_json_bytes(evidence), "canonical authenticated review evidence"
    )


def load_verified_static_bundle_with_review_evidence(
    static_root: Path,
    external_commitment_path: Path | None = None,
) -> tuple[Path, dict[str, Any], frozenset[str], dict[str, Any]]:
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
        verifier = integration.get("verify_static_with_review_evidence")
        if not callable(verifier):
            raise ProtocolError(
                "trusted integration lacks coherent static/review-evidence verification"
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
        or len(verified) != 3
        or not isinstance(verified[0], dict)
        or not isinstance(verified[1], (set, frozenset))
        or not isinstance(verified[2], dict)
    ):
        raise ProtocolError("trusted static verifier returned an invalid context")
    lock, raw_reviewer_ids, raw_review_evidence = verified
    if len(raw_reviewer_ids) != 11:
        raise ProtocolError("locked reviewer identity set is not exactly eleven actors")
    reviewer_ids = frozenset(
        require_production_actor_id(value, "locked reviewer actor ID")
        for value in raw_reviewer_ids
    )
    review_evidence = validate_authenticated_review_evidence(
        raw_review_evidence, reviewer_ids
    )
    if review_evidence["static_lock_sha256"] != commitment.get(
        "static_lock_sha256"
    ):
        raise ProtocolError(
            "authenticated review evidence does not equal the externally committed lock"
        )
    return root, lock, reviewer_ids, review_evidence


def load_verified_static_bundle(
    static_root: Path,
    external_commitment_path: Path | None = None,
) -> tuple[Path, dict[str, Any], frozenset[str]]:
    root, lock, reviewer_ids, _review_evidence = (
        load_verified_static_bundle_with_review_evidence(
            static_root, external_commitment_path
        )
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
            expected_reviewed_static_base=integration[
                "REVIEWED_STATIC_BUNDLE_BASE"
            ],
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


def load_aggregation_static_context(
    root: Path,
    static_lock: dict[str, Any],
    production_reviewer_ids: frozenset[str],
    authenticated_review_evidence: dict[str, Any],
) -> dict[str, Any]:
    """Load the immutable inputs shared by every runtime derivation stage."""

    evidence = validate_authenticated_review_evidence(
        authenticated_review_evidence, production_reviewer_ids
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
    integration = trusted_integration_module()
    declaration_bytes = (
        root / "static" / "integration" / "source-declaration.json"
    ).read_bytes()
    reviewed = integration["validate_reviewed_values"](
        read_json(root / "static" / "integration" / "integration-values.json"),
        declaration_bytes,
        expected_reviewed_static_base=integration[
            "REVIEWED_STATIC_BUNDLE_BASE"
        ],
    )
    preparation = run_trusted_module("prepare.py", "v5_aggregation_prepare")
    packages = read_json(root / "packages.json")
    preparation["validate_packages"](packages)
    targets_document = preparation["validate_targets"](
        read_json(root / "targets.json")
    )
    target_rows = {
        row["mode"]: row for row in documents["target-map.json"]["targets"]
    }
    if set(target_rows) != set(MODES):
        raise ProtocolError("aggregation target map does not contain every mode")
    rules = validate_defect_rules(
        read_json(root / "freeze" / "rules" / "defect-rules.json"), "READY"
    )
    atoms = {
        mode: validate_atom_manifest(
            read_json(root / "freeze" / "atoms" / f"{mode}.json"),
            mode,
            "READY",
        )
        for mode in MODES
    }
    controls = validate_control_manifest(
        read_json(root / "freeze" / "controls.json"),
        "READY",
        root / "freeze" / "atoms",
    )
    comparison = validate_comparison_predicate(
        read_json(root / "comparison-predicate.json"), "READY"
    )
    static_lock_sha = evidence["static_lock_sha256"]
    if sha256(canonical_json_bytes(static_lock)) != static_lock_sha:
        raise ProtocolError(
            "verified lock object does not equal the authenticated review-evidence lock"
        )
    return {
        "root": root,
        "static_lock": static_lock,
        "static_lock_sha256": static_lock_sha,
        "production_reviewer_ids": production_reviewer_ids,
        "review_evidence": evidence,
        "inventory": inventory,
        "gate_manifest": gate_manifest,
        "documents": documents,
        "reviewed": reviewed,
        "packages": packages,
        "targets_document": targets_document,
        "target_rows": target_rows,
        "blind_join": derive_blind_join(documents),
        "rules": rules,
        "atoms": atoms,
        "controls": controls,
        "comparison": comparison,
        "materiality_contract": materiality_contract,
        "rules_sha256": sha256((root / "aggregation-rules.json").read_bytes()),
    }


def _load_attempt_progress_locked(
    state_root: Path,
    production_reviewer_ids: frozenset[str],
    production_static_root: Path,
) -> dict[str, dict[str, Any]]:
    """Load STARTED/SEALED progress while the caller holds ``operation_lock``."""

    state = _verify_state_locked(
        state_root,
        production_reviewer_ids=production_reviewer_ids,
        production_static_root=production_static_root,
    )
    if state["staging_entries"]:
        raise ProtocolError("aggregation forbids incomplete envelope object stages")
    status_by_slot = {row["slot_id"]: row for row in state["slots"]}
    attempts: dict[str, dict[str, Any]] = {}
    for lease in _authoritative_leases(
        state_root, production_reviewer_ids=production_reviewer_ids
    ):
        launch = load_bound_launch(lease)
        assignment = launch["assignment_id"]
        if assignment in attempts:
            raise ProtocolError(f"duplicate canonical assignment: {assignment}")
        progress = status_by_slot[lease["slot_id"]]
        status = progress["status"]
        attempt: dict[str, Any] = {
            "status": status,
            "lease": lease,
            "launch": launch,
            "pointer": None,
            "envelope": None,
            "object_path": None,
            "primary_bytes": None,
        }
        if status == "SEALED":
            slot_path = state_root / "slots" / lease["slot_id"]
            pointer = read_json(slot_path / "canonical.json")
            terminal = read_json(slot_path / "terminal-claim.json")
            object_path = (
                state_root / "objects" / "sha256" / pointer["envelope_sha256"]
            )
            envelope = semantic_verify_envelope(
                object_path, lease, pointer, terminal
            )
            primary_relative = envelope_payload_relative_path(
                launch["output_path"]
            )
            primary_path = object_path / "payload" / Path(
                *primary_relative.parts
            )
            attempt.update(
                {
                    "pointer": pointer,
                    "envelope": envelope,
                    "object_path": object_path,
                    "primary_bytes": (
                        primary_path.read_bytes() if primary_path.is_file() else None
                    ),
                }
            )
        elif status != "STARTED":
            raise ProtocolError(
                f"aggregation cannot progress past incomplete terminal state: "
                f"{assignment}/{status}"
            )
        attempts[assignment] = attempt
    return attempts


def load_attempt_progress(
    static_root: Path,
    production_reviewer_ids: frozenset[str],
) -> dict[str, dict[str, Any]]:
    state_root = static_root / "runtime" / "state"
    if not state_root.is_dir() or state_root.is_symlink():
        raise ProtocolError("aggregation requires committed runtime/state")
    state_root = state_root.resolve()
    with operation_lock(state_root):
        return _load_attempt_progress_locked(
            state_root, production_reviewer_ids, static_root
        )


def load_canonical_attempt_inventory(
    static_root: Path,
    production_reviewer_ids: frozenset[str],
) -> dict[str, dict[str, Any]]:
    attempts = load_attempt_progress(static_root, production_reviewer_ids)
    unsealed = sorted(
        assignment
        for assignment, attempt in attempts.items()
        if attempt["status"] != "SEALED"
    )
    if unsealed:
        raise ProtocolError(f"bound aggregate has unsealed assignments: {unsealed}")
    return attempts


def require_sealed_attempt(
    attempts: dict[str, dict[str, Any]],
    assignment_id: str,
    expected_role: str,
    *,
    require_semantic_validity: bool,
) -> dict[str, Any]:
    attempt = attempts.get(assignment_id)
    if attempt is None:
        raise ProtocolError(f"missing canonical attempt: {assignment_id}")
    if attempt["status"] != "SEALED":
        raise ProtocolError(f"attempt is not sealed: {assignment_id}")
    if (
        attempt["launch"]["role"] != expected_role
        or attempt["pointer"] is None
        or attempt["primary_bytes"] is None
    ):
        raise ProtocolError(f"sealed attempt has no usable primary output: {assignment_id}")
    if require_semantic_validity and (
        attempt["pointer"]["format_valid"] is not True
        or attempt["pointer"]["semantic_valid"] is not True
    ):
        raise ProtocolError(f"evaluator attempt is not semantically valid: {assignment_id}")
    return attempt


def sealed_attempt_envelopes(
    attempts: dict[str, dict[str, Any]], assignment_ids: set[str]
) -> dict[str, str]:
    result: dict[str, str] = {}
    for assignment_id in sorted(assignment_ids):
        attempt = attempts[assignment_id]
        pointer = attempt.get("pointer")
        if (
            attempt.get("status") != "SEALED"
            or not isinstance(pointer, dict)
            or not isinstance(pointer.get("envelope_sha256"), str)
            or not HEX64.fullmatch(pointer["envelope_sha256"])
        ):
            raise ProtocolError(
                f"aggregation stage prerequisite is not sealed: {assignment_id}"
            )
        result[assignment_id] = pointer["envelope_sha256"]
    return result


def exact_progress_partition(
    attempts: dict[str, dict[str, Any]],
    *,
    completed: set[str],
    eligible: set[str],
    label: str,
) -> tuple[set[str], set[str]]:
    allowed = completed | eligible
    missing_completed = completed - set(attempts)
    if missing_completed:
        raise ProtocolError(f"{label} lost completed attempts: {sorted(missing_completed)}")
    sealed = {
        assignment
        for assignment in eligible
        if assignment in attempts and attempts[assignment]["status"] == "SEALED"
    }
    started = {
        assignment
        for assignment in eligible
        if assignment in attempts and attempts[assignment]["status"] == "STARTED"
    }
    extras = set(attempts) - allowed
    if sealed != eligible and extras:
        raise ProtocolError(f"{label} has premature or unknown attempts: {sorted(extras)}")
    return sealed, started


def aggregation_phase_failure_assignments(
    attempts: dict[str, dict[str, Any]],
    assignments: set[str],
    *,
    report_phase: bool,
) -> set[str]:
    """Return exactly the sealed phase outputs that prevent semantic derivation."""

    failures: set[str] = set()
    for assignment_id in sorted(assignments):
        attempt = attempts.get(assignment_id)
        if attempt is None or attempt.get("status") != "SEALED":
            raise ProtocolError(
                f"terminal-failure check requires a sealed attempt: {assignment_id}"
            )
        pointer = attempt.get("pointer")
        if not isinstance(pointer, dict):
            raise ProtocolError(
                f"terminal-failure check lacks a canonical pointer: {assignment_id}"
            )
        if report_phase:
            if (
                attempt.get("primary_bytes") is None
                or pointer["semantic_valid"] is not True
            ):
                failures.add(assignment_id)
        elif (
            attempt.get("primary_bytes") is None
            or pointer["format_valid"] is not True
            or pointer["semantic_valid"] is not True
        ):
            failures.add(assignment_id)
    return failures


def derive_report_products(
    context: dict[str, Any],
    attempts: dict[str, dict[str, Any]],
) -> tuple[dict[str, bytes], dict[str, Any]]:
    """Derive Stage 01 solely from the 120 canonical report envelopes."""

    root = context["root"]
    documents = context["documents"]
    blind_join = context["blind_join"]
    by_run = {row["run_id"]: row for row in blind_join}
    expected_runs = {f"r{index:03d}" for index in range(1, 121)}
    report_attempts: dict[str, dict[str, Any]] = {}
    static_launches = {
        launch["run_id"]: launch for launch in documents["report-launch-records"]
    }
    for run_id in sorted(expected_runs):
        attempt = require_sealed_attempt(
            attempts,
            run_id,
            "report",
            require_semantic_validity=False,
        )
        joined = by_run[run_id]
        if (
            attempt["launch"]["run_id"] != run_id
            or attempt["launch"]["mode"] != joined["mode"]
            or attempt["launch"] != static_launches[run_id]
        ):
            raise ProtocolError(f"canonical report launch drifted: {run_id}")
        report_attempts[run_id] = attempt

    counter = run_trusted_module("word_count.py", "v5_stage_word_counter")
    count_words = counter["count_words"]
    word_records: list[dict[str, Any]] = []
    projection_records: list[dict[str, Any]] = []
    projected_reports: dict[tuple[str, str], bytes] = {}
    scorer_receipts: dict[tuple[str, str], dict[str, Any]] = {}
    for run_id in sorted(expected_runs):
        attempt = report_attempts[run_id]
        raw = attempt["primary_bytes"]
        joined = by_run[run_id]
        mode = joined["mode"]
        word_count = count_words(raw)
        word_records.append(
            {
                "run_id": run_id,
                "receipt": {
                    "schema_version": 1,
                    "status": "COUNTED",
                    "algorithm_id": "unicode-whitespace-runs-python-v1",
                    "report_sha256": sha256(raw),
                    "word_count": word_count,
                    "word_cap": context["target_rows"][mode]["word_cap"],
                    "valid": word_count
                    <= context["target_rows"][mode]["word_cap"],
                },
            }
        )
        inventory = derive_report_secret_inventory(
            root,
            attempt["launch"],
            attempt["lease"],
            context["reviewed"],
            context["packages"],
            context["target_rows"][mode],
        )
        projected, scorer_receipt, audit_receipt = project_report_for_scorer(
            joined["label"], raw, inventory
        )
        projection_records.append(
            {
                "run_id": run_id,
                "mode": mode,
                "label": joined["label"],
                "secret_inventory_sha256": sha256(
                    canonical_json_bytes(inventory)
                ),
                "secret_inventory": inventory,
                "receipt_sha256": sha256(
                    canonical_json_bytes(audit_receipt)
                ),
                "receipt": audit_receipt,
            }
        )
        projected_reports[(mode, joined["label"])] = projected
        scorer_receipts[(mode, joined["label"])] = scorer_receipt
    word_manifest = validate_word_count_manifest(
        {
            "schema_version": 1,
            "status": "COMPLETE",
            "algorithm_id": "unicode-whitespace-runs-python-v1",
            "records": word_records,
        }
    )
    projection_manifest = validate_projection_audit_manifest(
        {
            "schema_version": 1,
            "status": "COMPLETE",
            "records": projection_records,
        }
    )
    files: dict[str, bytes] = {
        "word-counts.json": canonical_json_bytes(word_manifest),
        "projection-audit-manifest.json": canonical_json_bytes(
            projection_manifest
        ),
    }
    scorer_packets: dict[str, dict[str, Any]] = {}
    scorer_launches: dict[str, dict[str, Any]] = {}
    for mode in MODES:
        for scorer in SCORERS:
            assignment = f"{mode}-{scorer}"
            labels = next(
                row["labels_in_order"]
                for row in documents["presentation-orders.json"]["presentations"]
                if row["claim"] == assignment
            )
            packet = build_score_input_packet(
                mode,
                scorer,
                labels,
                {
                    label: projected_reports[(mode, label)] for label in LABELS
                },
                {
                    label: scorer_receipts[(mode, label)] for label in LABELS
                },
                context["atoms"][mode],
                context["rules"],
                (root / "freeze" / "oracle" / f"{mode}.md").read_bytes(),
                (root / "freeze" / "allowlists" / f"{mode}.txt").read_bytes(),
                (root / "freeze" / "authority" / "propositions.json").read_bytes(),
            )
            packet_bytes = canonical_json_bytes(packet)
            launch, _row = build_expected_evaluator_launch(
                root, documents, assignment, packet_bytes
            )
            scorer_packets[assignment] = packet
            scorer_launches[assignment] = launch
            files[f"packets/scorers/{assignment}.json"] = packet_bytes
            files[f"launches/scorers/{assignment}.json"] = canonical_json_bytes(
                launch
            )
    return files, {
        "word_manifest": word_manifest,
        "projection_manifest": projection_manifest,
        "report_attempts": report_attempts,
        "projected_reports": projected_reports,
        "scorer_receipts": scorer_receipts,
        "scorer_packets": scorer_packets,
        "scorer_launches": scorer_launches,
    }


def require_staged_evaluator_attempt(
    attempts: dict[str, dict[str, Any]],
    assignment_id: str,
    expected_role: str,
    expected_packet: dict[str, Any],
    expected_launch: dict[str, Any],
) -> dict[str, Any]:
    """Validate a sealed evaluator against immutable stage bytes only."""

    attempt = require_sealed_attempt(
        attempts,
        assignment_id,
        expected_role,
        require_semantic_validity=True,
    )
    expected_packet_bytes = canonical_json_bytes(expected_packet)
    if (
        attempt["launch"] != expected_launch
        or load_bound_launch(attempt["lease"]) != expected_launch
        or load_bound_input_packet_bytes(attempt["lease"])
        != expected_packet_bytes
    ):
        raise ProtocolError(
            f"evaluator attempt is not bound to its authoritative stage: {assignment_id}"
        )
    return attempt


def derive_scorer_products(
    context: dict[str, Any],
    attempts: dict[str, dict[str, Any]],
    report_products: dict[str, Any],
) -> tuple[dict[str, bytes], dict[str, Any]]:
    """Derive Stage 02 from the sixteen canonical direct-score attempts."""

    root = context["root"]
    documents = context["documents"]
    files: dict[str, bytes] = {}
    direct_scores: dict[tuple[str, str], dict[str, Any]] = {}
    scorer_attempts: dict[tuple[str, str], dict[str, Any]] = {}
    consistency_packets: dict[str, dict[str, Any]] = {}
    consistency_launches: dict[str, dict[str, Any]] = {}
    for mode in MODES:
        score_inputs = [
            report_products["scorer_packets"][f"{mode}-{scorer}"]
            for scorer in SCORERS
        ]
        mode_scores: list[dict[str, Any]] = []
        for scorer, packet in zip(SCORERS, score_inputs):
            assignment = f"{mode}-{scorer}"
            attempt = require_staged_evaluator_attempt(
                attempts,
                assignment,
                "scorer",
                packet,
                report_products["scorer_launches"][assignment],
            )
            score = attempt_output_json(attempt, f"{mode} direct score {scorer}")
            validate_direct_score(
                score,
                context["atoms"][mode],
                context["rules"],
                scorer,
                packet,
            )
            direct_scores[(mode, scorer)] = score
            scorer_attempts[(mode, scorer)] = attempt
            mode_scores.append(score)
        packet = build_consistency_packet(
            mode_scores[0],
            mode_scores[1],
            score_inputs[0],
            score_inputs[1],
            context["atoms"][mode],
            context["rules"],
        )
        consistency_packets[mode] = packet
        packet_bytes = canonical_json_bytes(packet)
        files[f"packets/consistency/{mode}.json"] = packet_bytes
        for reviewer in CONSISTENCY_REVIEWERS:
            assignment = f"{mode}-{reviewer}"
            launch, _row = build_expected_evaluator_launch(
                root, documents, assignment, packet_bytes
            )
            consistency_launches[assignment] = launch
            files[f"launches/consistency/{assignment}.json"] = canonical_json_bytes(
                launch
            )
    return files, {
        "direct_scores": direct_scores,
        "scorer_attempts": scorer_attempts,
        "consistency_packets": consistency_packets,
        "consistency_launches": consistency_launches,
    }


def derive_consistency_products(
    context: dict[str, Any],
    attempts: dict[str, dict[str, Any]],
    report_products: dict[str, Any],
    scorer_products: dict[str, Any],
) -> tuple[dict[str, bytes], dict[str, Any]]:
    """Derive Stage 03 and its exact conditional mode-adjudicator set."""

    root = context["root"]
    documents = context["documents"]
    files: dict[str, bytes] = {}
    consistency_outputs: dict[tuple[str, str], dict[str, Any]] = {}
    consistency_attempts: dict[tuple[str, str], dict[str, Any]] = {}
    adjudication_packets: dict[str, dict[str, Any]] = {}
    adjudication_launches: dict[str, dict[str, Any]] = {}
    dispositions: list[dict[str, Any]] = []
    for mode in MODES:
        packet = scorer_products["consistency_packets"][mode]
        outputs: list[dict[str, Any]] = []
        for reviewer in CONSISTENCY_REVIEWERS:
            assignment = f"{mode}-{reviewer}"
            attempt = require_staged_evaluator_attempt(
                attempts,
                assignment,
                "consistency",
                packet,
                scorer_products["consistency_launches"][assignment],
            )
            output = attempt_output_json(
                attempt, f"{mode} consistency review {reviewer}"
            )
            validate_consistency(
                output,
                context["atoms"][mode],
                context["rules"],
                packet,
                reviewer,
            )
            consistency_outputs[(mode, reviewer)] = output
            consistency_attempts[(mode, reviewer)] = attempt
            outputs.append(output)
        score_inputs = [
            report_products["scorer_packets"][f"{mode}-{scorer}"]
            for scorer in SCORERS
        ]
        direct_scores = [
            scorer_products["direct_scores"][(mode, scorer)]
            for scorer in SCORERS
        ]
        adjudication_packet = build_adjudication_packet(
            direct_scores[0],
            direct_scores[1],
            score_inputs[0],
            score_inputs[1],
            outputs[0],
            outputs[1],
            context["atoms"][mode],
            context["rules"],
        )
        adjudication_packets[mode] = adjudication_packet
        packet_bytes = canonical_json_bytes(adjudication_packet)
        files[f"packets/adjudication/{mode}.json"] = packet_bytes
        assignment = f"{mode}-a1"
        required = bool(adjudication_packet["cells"])
        dispositions.append(
            {
                "mode": mode,
                "assignment_id": assignment,
                "packet_sha256": sha256(packet_bytes),
                "disposition": (
                    "LAUNCH_REQUIRED" if required else "NO_LAUNCH_EMPTY_PACKET"
                ),
            }
        )
        if required:
            launch, _row = build_expected_evaluator_launch(
                root, documents, assignment, packet_bytes
            )
            adjudication_launches[assignment] = launch
            files[f"launches/adjudication/{assignment}.json"] = canonical_json_bytes(
                launch
            )
    disposition_document = {
        "schema_version": 1,
        "status": "DERIVED",
        "records": dispositions,
    }
    files["adjudication-dispositions.json"] = canonical_json_bytes(
        disposition_document
    )
    return files, {
        "consistency_outputs": consistency_outputs,
        "consistency_attempts": consistency_attempts,
        "adjudication_packets": adjudication_packets,
        "adjudication_launches": adjudication_launches,
        "adjudication_dispositions": disposition_document,
        "required_adjudicators": set(adjudication_launches),
    }


def derive_score_products(
    context: dict[str, Any],
    attempts: dict[str, dict[str, Any]],
    report_products: dict[str, Any],
    scorer_products: dict[str, Any],
    consistency_products: dict[str, Any],
) -> tuple[dict[str, bytes], dict[str, Any]]:
    """Derive Stage 04 final scores and the complete materiality review input."""

    root = context["root"]
    documents = context["documents"]
    finals: dict[str, dict[str, Any]] = {}
    bundle_rows: list[dict[str, Any]] = []
    adjudication_attempts: dict[str, dict[str, Any]] = {}
    for mode in MODES:
        score_inputs = [
            report_products["scorer_packets"][f"{mode}-{scorer}"]
            for scorer in SCORERS
        ]
        direct_scores = [
            scorer_products["direct_scores"][(mode, scorer)]
            for scorer in SCORERS
        ]
        consistency_outputs = [
            consistency_products["consistency_outputs"][(mode, reviewer)]
            for reviewer in CONSISTENCY_REVIEWERS
        ]
        packet = consistency_products["adjudication_packets"][mode]
        assignment = f"{mode}-a1"
        if assignment in consistency_products["required_adjudicators"]:
            attempt = require_staged_evaluator_attempt(
                attempts,
                assignment,
                "adjudicator",
                packet,
                consistency_products["adjudication_launches"][assignment],
            )
            adjudication = attempt_output_json(
                attempt, f"{mode} adjudication"
            )
            validate_adjudication(adjudication, packet)
            adjudication_attempts[assignment] = attempt
            adjudication_digest = sha256(attempt["primary_bytes"])
            adjudicator_envelope = attempt["pointer"]["envelope_sha256"]
        else:
            if assignment in attempts:
                raise ProtocolError(
                    f"empty mode adjudication packet has an attempt: {assignment}"
                )
            adjudication = None
            adjudication_digest = None
            adjudicator_envelope = None
        final = merge_final_scores(
            direct_scores[0],
            direct_scores[1],
            score_inputs[0],
            score_inputs[1],
            consistency_outputs[0],
            consistency_outputs[1],
            context["atoms"][mode],
            context["rules"],
            adjudication,
        )
        validate_final_score(final, context["atoms"][mode], context["rules"])
        finals[mode] = final
        scorer_attempts = [
            scorer_products["scorer_attempts"][(mode, scorer)]
            for scorer in SCORERS
        ]
        consistency_attempts = [
            consistency_products["consistency_attempts"][(mode, reviewer)]
            for reviewer in CONSISTENCY_REVIEWERS
        ]
        bundle_rows.append(
            {
                "mode": mode,
                "score_input_packet_digests": [
                    item["lease"]["input_packet_sha256"]
                    for item in scorer_attempts
                ],
                "direct_score_digests": [
                    sha256(item["primary_bytes"]) for item in scorer_attempts
                ],
                "consistency_input_packet_digest": consistency_attempts[0][
                    "lease"
                ]["input_packet_sha256"],
                "consistency_review_digests": [
                    sha256(item["primary_bytes"]) for item in consistency_attempts
                ],
                "adjudication_packet_digest": sha256(
                    canonical_json_bytes(packet)
                ),
                "adjudication_digest": adjudication_digest,
                "final_score_digest": sha256(canonical_json_bytes(final)),
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
    scoring_bundle = validate_scoring_bundle_manifest(
        {"schema_version": 1, "status": "BOUND", "modes": bundle_rows}
    )

    projection_by_run = {
        row["run_id"]: row
        for row in report_products["projection_manifest"]["records"]
    }
    joined_reports: list[dict[str, Any]] = []
    for row in context["blind_join"]:
        final_report = next(
            item
            for item in finals[row["mode"]]["reports"]
            if item["label"] == row["label"]
        )
        audit = projection_by_run[row["run_id"]]["receipt"]
        if ("GH12" in final_report["hard_errors"]) is not bool(
            audit["replacements"]
        ):
            raise ProtocolError(
                f"GH12 does not equal projection redaction presence: {row['run_id']}"
            )
        raw = report_products["report_attempts"][row["run_id"]][
            "primary_bytes"
        ]
        try:
            raw_text = raw.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise ProtocolError(
                f"canonical report is not UTF-8: {row['run_id']}"
            ) from error
        joined_reports.append(
            {
                **row,
                "raw_report_sha256": sha256(raw),
                "raw_report": raw_text,
                "projected_report_sha256": audit["projected_report_sha256"],
                "final_report": final_report,
            }
        )

    candidate_by_mode = {
        mode: [
            row
            for row in joined_reports
            if row["mode"] == mode and row["condition_role"] == "v5"
        ]
        for mode in MODES
    }
    control_records: list[dict[str, Any]] = []
    for control in context["controls"]["controls"]:
        candidates = candidate_by_mode[control["mode"]]
        passed = all(
            all(
                next(
                    atom
                    for atom in row["final_report"]["atoms"]
                    if atom["id"] == atom_id
                )["certificate_decision"]
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
                "candidate_run_ids": sorted(
                    row["run_id"] for row in candidates
                ),
            }
        )
    control_results = validate_control_results(
        {"schema_version": 1, "status": "DERIVED", "records": control_records},
        context["controls"],
        "READY",
        root / "freeze" / "atoms",
    )

    candidate_package = context["packages"]["packages"]["v5"]
    if not isinstance(candidate_package, dict):
        raise ProtocolError("integrated bundle lacks the V5 candidate package")
    source_records = {
        record["name"]: record
        for record in context["review_evidence"]["source_review_receipts"]
    }
    snapshot_records = {
        record["hook_id"]: record
        for record in context["review_evidence"]["snapshot_review_receipts"]
    }
    scope_payloads = {
        "V5_CANDIDATE_REPORTS": {
            "schema_version": 1,
            "status": "COMPLETE",
            "reports": [
                row for row in joined_reports if row["condition_role"] == "v5"
            ],
        },
        "CANDIDATE_PACKAGE": {
            "schema_version": 1,
            "status": "CONTENT-BOUND",
            "identity": candidate_package,
            "tree": readable_tree_snapshot(root / candidate_package["source_path"]),
        },
        "HARNESS_PROTOCOL": {
            "schema_version": 1,
            "status": "STATIC-LOCKED",
            "static_lock_sha256": context["static_lock_sha256"],
            "tree": readable_tree_snapshot(root, exclude_top_level={"runtime"}),
        },
        "ADVERSARIAL_AND_COHERENCE_REVIEWS": {
            "schema_version": 1,
            "status": "AUTHENTICATED-COMPLETE",
            "static_lock_sha256": context["static_lock_sha256"],
            "source_review_receipts": context["review_evidence"][
                "source_review_receipts"
            ],
            "snapshot_review_receipts": context["review_evidence"][
                "snapshot_review_receipts"
            ],
        },
    }
    materiality_packet = build_materiality_review_packet(
        scope_payloads, context["materiality_contract"], "READY"
    )
    packet_bytes = canonical_json_bytes(materiality_packet)
    materiality_launches: dict[str, dict[str, Any]] = {}
    files: dict[str, bytes] = {
        "scoring-bundle-manifest.json": canonical_json_bytes(scoring_bundle),
        "packets/materiality-review.json": packet_bytes,
    }
    for mode in MODES:
        files[f"final-scores/{mode}.json"] = canonical_json_bytes(finals[mode])
    for index, scope in enumerate(MATERIALITY_SCOPES, start=1):
        path = f"materiality-scopes/{index:02d}-{scope.lower().replace('_', '-')}.json"
        files[path] = canonical_json_bytes(scope_payloads[scope])
    for reviewer in MATERIALITY_REVIEWERS:
        launch, _row = build_expected_evaluator_launch(
            root, documents, reviewer, packet_bytes
        )
        materiality_launches[reviewer] = launch
        files[f"launches/materiality/{reviewer}.json"] = canonical_json_bytes(
            launch
        )
    return files, {
        "finals": finals,
        "scoring_bundle": scoring_bundle,
        "adjudication_attempts": adjudication_attempts,
        "joined_reports": joined_reports,
        "candidate_by_mode": candidate_by_mode,
        "control_results": control_results,
        "source_review_records": source_records,
        "snapshot_review_records": snapshot_records,
        "scope_payloads": scope_payloads,
        "materiality_packet": materiality_packet,
        "materiality_launches": materiality_launches,
    }


def derive_materiality_review_products(
    context: dict[str, Any],
    attempts: dict[str, dict[str, Any]],
    score_products: dict[str, Any],
) -> tuple[dict[str, bytes], dict[str, Any]]:
    """Derive Stage 05 and the exact conditional materiality adjudicator."""

    packet = score_products["materiality_packet"]
    reviews: list[dict[str, Any]] = []
    reviewer_attempts: dict[str, dict[str, Any]] = {}
    for reviewer in MATERIALITY_REVIEWERS:
        attempt = require_staged_evaluator_attempt(
            attempts,
            reviewer,
            "materiality-reviewer",
            packet,
            score_products["materiality_launches"][reviewer],
        )
        review = attempt_output_json(attempt, f"materiality review {reviewer}")
        validate_materiality_review(review, packet, reviewer, "READY")
        reviews.append(review)
        reviewer_attempts[reviewer] = attempt
    adjudication_packet = build_materiality_adjudication_packet(
        packet, reviews[0], reviews[1], "READY"
    )
    packet_bytes = canonical_json_bytes(adjudication_packet)
    required = bool(adjudication_packet["cells"])
    disposition = {
        "schema_version": 1,
        "status": "DERIVED",
        "assignment_id": "ma1",
        "packet_sha256": sha256(packet_bytes),
        "disposition": (
            "LAUNCH_REQUIRED" if required else "NO_LAUNCH_EMPTY_PACKET"
        ),
    }
    files = {
        "packets/materiality-adjudication.json": packet_bytes,
        "materiality-adjudication-disposition.json": canonical_json_bytes(
            disposition
        ),
    }
    launch: dict[str, Any] | None = None
    if required:
        launch, _row = build_expected_evaluator_launch(
            context["root"],
            context["documents"],
            "ma1",
            packet_bytes,
        )
        files["launches/materiality/ma1.json"] = canonical_json_bytes(launch)
    return files, {
        "reviews": reviews,
        "reviewer_attempts": reviewer_attempts,
        "adjudication_packet": adjudication_packet,
        "adjudication_launch": launch,
        "requires_adjudicator": required,
        "disposition": disposition,
    }


def build_runtime_integration_receipt(
    hook_id: str,
    coordinator_actor_id: str,
    input_digests: dict[str, str],
    output_digests: dict[str, str],
) -> dict[str, Any]:
    phase = INTEGRATION_HOOK_PHASES[hook_id]
    if phase not in ("RUNTIME_COLLECTION", "POSTRUN_AGGREGATE"):
        raise ProtocolError(f"hook is not a post-lock runtime hook: {hook_id}")
    coordinator_actor_id = require_production_actor_id(
        coordinator_actor_id, "aggregation coordinator actor ID"
    )
    receipt = {
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
            "identity": coordinator_actor_id,
            "role": "V5_RUNTIME_COORDINATOR",
            "implementation": "protocol.advance_aggregation",
            "version": "v5-staged-aggregation-v1",
        },
        "input_digests": input_digests,
        "output_digests": output_digests,
        "result": {
            "summary": (
                f"Trusted staged aggregation deterministically revalidated {hook_id} "
                "from the authenticated static bundle and canonical sealed attempts."
            ),
            "checks": [
                {
                    "id": "EXACT-DERIVATION-RECOMPUTED",
                    "status": "PASS",
                    "evidence": (
                        f"{hook_id} inputs and outputs equal the protocol-owned "
                        "deterministic derivation."
                    ),
                }
            ],
        },
    }
    return validate_integration_receipt(receipt, hook_id, phase)


def build_bound_aggregate_receipts(
    aggregate: dict[str, Any], coordinator_actor_id: str
) -> dict[str, dict[str, Any]]:
    aggregate = validate_aggregate_context_document(aggregate)
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
    receipts = {
        hook_id: build_runtime_integration_receipt(
            hook_id, coordinator_actor_id, common_inputs, outputs
        )
        for hook_id, outputs in runtime_outputs.items()
    }
    aggregate_sha = sha256(canonical_json_bytes(aggregate))
    receipts["H-DERIVE-AGGREGATE-CONTEXT"] = build_runtime_integration_receipt(
        "H-DERIVE-AGGREGATE-CONTEXT",
        coordinator_actor_id,
        common_inputs,
        {"aggregate_context_sha256": aggregate_sha},
    )
    bind_inputs = {
        "static_lock_sha256": aggregate["static_lock_sha256"],
        "rules_sha256": aggregate["rules_sha256"],
        "aggregate_context_sha256": aggregate_sha,
        **{
            f"receipt::{hook_id}": sha256(
                canonical_json_bytes(receipts[hook_id])
            )
            for hook_id in PRE_BIND_RECEIPT_HOOK_IDS
        },
    }
    receipts["H-BIND-CONTEXT-INPUT-DIGESTS"] = build_runtime_integration_receipt(
        "H-BIND-CONTEXT-INPUT-DIGESTS",
        coordinator_actor_id,
        bind_inputs,
        {
            "bound_gate_context_sha256": sha256(
                canonical_json_bytes(bind_inputs)
            )
        },
    )
    if set(receipts) != set(POSTLOCK_RECEIPT_HOOK_IDS):
        raise ProtocolError("derived post-lock receipt inventory is not exact")
    return receipts


def derive_final_aggregation_products(
    context: dict[str, Any],
    attempts: dict[str, dict[str, Any]],
    report_products: dict[str, Any],
    scorer_products: dict[str, Any],
    consistency_products: dict[str, Any],
    score_products: dict[str, Any],
    materiality_products: dict[str, Any],
    coordinator_actor_id: str,
) -> tuple[dict[str, bytes], dict[str, Any]]:
    """Derive the one authoritative final tree without caller-authored inputs."""

    if materiality_products["requires_adjudicator"]:
        attempt = require_staged_evaluator_attempt(
            attempts,
            "ma1",
            "materiality-adjudicator",
            materiality_products["adjudication_packet"],
            materiality_products["adjudication_launch"],
        )
        materiality_adjudication = attempt_output_json(
            attempt, "materiality adjudication"
        )
        validate_materiality_adjudication(
            materiality_adjudication,
            materiality_products["adjudication_packet"],
            "READY",
        )
    else:
        if "ma1" in attempts:
            raise ProtocolError(
                "empty materiality adjudication packet has an ma1 attempt"
            )
        materiality_adjudication = None
    materiality_ledger = validate_materiality_ledger(
        merge_materiality_ledger(
            score_products["materiality_packet"],
            materiality_products["reviews"][0],
            materiality_products["reviews"][1],
            materiality_adjudication,
            "READY",
        )
    )

    expected_assignments = {
        *(f"r{index:03d}" for index in range(1, 121)),
        *(f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS),
        *(
            f"{mode}-{reviewer}"
            for mode in MODES
            for reviewer in CONSISTENCY_REVIEWERS
        ),
        *consistency_products["required_adjudicators"],
        *MATERIALITY_REVIEWERS,
    }
    if materiality_products["requires_adjudicator"]:
        expected_assignments.add("ma1")
    if set(attempts) != expected_assignments:
        raise ProtocolError(
            "final aggregation attempt inventory is not exact; "
            f"missing={sorted(expected_assignments - set(attempts))}, "
            f"extra={sorted(set(attempts) - expected_assignments)}"
        )
    if any(attempt["status"] != "SEALED" for attempt in attempts.values()):
        raise ProtocolError("final aggregation contains an unsealed attempt")

    candidate_by_mode = score_products["candidate_by_mode"]
    focused_recall = all(
        atom["certificate_decision"] == "PASS"
        for rows in candidate_by_mode.values()
        for row in rows
        for atom in row["final_report"]["atoms"]
    )
    proof_quality = all(
        row["passed"]
        for row in score_products["control_results"]["records"]
        if row["family"] == "PROOF_QUALITY"
    )
    classification_controls = all(
        row["passed"]
        for row in score_products["control_results"]["records"]
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
        atom_ids = [
            atom["id"]
            for atom in score_products["finals"][mode]["reports"][0]["atoms"]
        ]
        for atom_id in atom_ids:
            counts = {
                condition: sum(
                    next(
                        atom
                        for atom in row["final_report"]["atoms"]
                        if atom["id"] == atom_id
                    )["certificate_decision"]
                    == "PASS"
                    for row in score_products["joined_reports"]
                    if row["mode"] == mode
                    and row["condition_role"] == condition
                )
                for condition in ("v5", "v4", "no_skill")
            }
            comparison_pass = (
                comparison_pass
                and counts["v5"] >= counts["v4"]
                and counts["v5"] >= counts["no_skill"]
            )

    word_by_run = {
        row["run_id"]: row["receipt"]
        for row in report_products["word_manifest"]["records"]
    }
    invalid_output_count = sum(
        not (
            report_products["report_attempts"][run_id]["pointer"]["format_valid"]
            and report_products["report_attempts"][run_id]["pointer"][
                "semantic_valid"
            ]
            and word_by_run[run_id]["valid"]
        )
        for run_id in sorted(report_products["report_attempts"])
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
    atom_documents = context["atoms"]
    oracle_documents = {
        "schema_version": 1,
        "snapshot_oracle_coverage_receipt": score_products[
            "snapshot_review_records"
        ]["H-VALIDATE-ORACLE-COVERAGE"],
        "source_oracle_review_receipts": [
            score_products["source_review_records"][name]
            for name in ("oracle-review-1.json", "oracle-review-2.json")
        ],
    }
    coherence_document = {
        "schema_version": 1,
        "source_coherence_review_receipt": score_products[
            "source_review_records"
        ]["coherence-review.json"],
    }
    input_digests = {
        "schedule_slots_sha256": sha256(
            canonical_json_bytes(context["documents"]["launch-schedule.json"])
        ),
        "envelopes_sha256": sha256(canonical_json_bytes(envelope_summary)),
        "word_counts_sha256": sha256(
            canonical_json_bytes(report_products["word_manifest"])
        ),
        "atom_manifests_sha256": sha256(canonical_json_bytes(atom_documents)),
        "oracle_receipts_sha256": sha256(canonical_json_bytes(oracle_documents)),
        "blind_join_sha256": sha256(
            canonical_json_bytes(context["blind_join"])
        ),
        "joined_reports_sha256": sha256(
            canonical_json_bytes(score_products["joined_reports"])
        ),
        "projection_audit_manifest_sha256": sha256(
            canonical_json_bytes(report_products["projection_manifest"])
        ),
        "scoring_bundle_manifest_sha256": sha256(
            canonical_json_bytes(score_products["scoring_bundle"])
        ),
        "control_manifest_sha256": sha256(
            canonical_json_bytes(context["controls"])
        ),
        "control_results_sha256": sha256(
            canonical_json_bytes(score_products["control_results"])
        ),
        "materiality_ledger_sha256": sha256(
            canonical_json_bytes(materiality_ledger)
        ),
        "comparison_predicate_sha256": sha256(
            canonical_json_bytes(context["comparison"])
        ),
        "coherence_review_sha256": sha256(
            canonical_json_bytes(coherence_document)
        ),
    }
    oracle_coverage = score_products["snapshot_review_records"][
        "H-VALIDATE-ORACLE-COVERAGE"
    ]["receipt"]
    source_oracle_receipts = [
        score_products["source_review_records"][name]["receipt"]
        for name in ("oracle-review-1.json", "oracle-review-2.json")
    ]
    coherence_receipt = score_products["source_review_records"][
        "coherence-review.json"
    ]["receipt"]
    core = {
        "schema_version": 1,
        "status": "DERIVED",
        "builder_id": AGGREGATE_BUILDER_ID,
        "static_lock_sha256": context["static_lock_sha256"],
        "rules_sha256": context["rules_sha256"],
        "input_digests": input_digests,
        "context": {
            "oracle": {
                "coverage_pass": oracle_coverage["status"] == "PASS"
                and all(
                    receipt["status"] == "PASS"
                    for receipt in source_oracle_receipts
                )
            },
            "collection": {
                "complete": len(report_products["report_attempts"]) == 120,
                "invalid_output_count": invalid_output_count,
            },
            "scores": {
                "focused_recall_pass": focused_recall,
                "proof_quality_pass": proof_quality,
                "controls_pass": classification_controls,
                "hard_error_count": hard_error_count,
                "global_defect_count": global_defect_count,
                "material_finding_count": sum(
                    finding["blocking"]
                    for finding in materiality_ledger["findings"]
                ),
            },
            "comparison": {"predicate_pass": comparison_pass},
            "review": {
                "coherence_pass": coherence_receipt["status"] == "PASS"
            },
        },
    }
    aggregate = validate_aggregate_context_document(
        {**core, "binding_sha256": sha256(canonical_json_bytes(core))}
    )
    receipts = build_bound_aggregate_receipts(aggregate, coordinator_actor_id)
    files: dict[str, bytes] = {
        "inputs/word-counts.json": canonical_json_bytes(
            report_products["word_manifest"]
        ),
        "inputs/projection-audit-manifest.json": canonical_json_bytes(
            report_products["projection_manifest"]
        ),
        "inputs/scoring-bundle-manifest.json": canonical_json_bytes(
            score_products["scoring_bundle"]
        ),
        "inputs/materiality-ledger.json": canonical_json_bytes(
            materiality_ledger
        ),
        "aggregate-context.json": canonical_json_bytes(aggregate),
    }
    for mode in MODES:
        files[f"inputs/final-scores/{mode}.json"] = canonical_json_bytes(
            score_products["finals"][mode]
        )
    for hook_id in POSTLOCK_RECEIPT_HOOK_IDS:
        files[f"integration-receipts/{hook_id}.json"] = canonical_json_bytes(
            receipts[hook_id]
        )
    return files, {
        "aggregate": aggregate,
        "materiality_ledger": materiality_ledger,
        "receipts": receipts,
        "expected_assignments": expected_assignments,
    }


def validate_aggregation_progress(value: Any) -> dict[str, Any]:
    progress = require_exact_keys(
        value,
        {
            "schema_version",
            "status",
            "current_stage",
            "coordinator_actor_id",
            "published_stages",
            "sealed_assignments",
            "started_assignments",
            "leaseable_assignments",
            "pending_assignments",
            "final_aggregate_sha256",
            "terminal_failure_sha256",
        },
        "aggregation progress",
    )
    status = progress["status"]
    current_stage = progress["current_stage"]
    if (
        progress["schema_version"] != 1
        or status
        not in (
            "WAITING",
            "DERIVABLE",
            "PUBLISHED",
            "COMPLETE",
            "TERMINAL-FAILURE",
        )
        or current_stage not in (*AGGREGATION_STAGE_ORDER, "reports")
    ):
        raise ProtocolError("aggregation progress identity/status is invalid")
    require_production_actor_id(
        progress["coordinator_actor_id"], "aggregation coordinator actor ID"
    )
    if not isinstance(progress["published_stages"], list):
        raise ProtocolError("aggregation progress stage inventory must be a list")
    published: list[dict[str, str]] = []
    for raw in progress["published_stages"]:
        row = require_exact_keys(
            raw,
            {"stage_id", "manifest_sha256"},
            "aggregation progress stage",
        )
        if (
            row["stage_id"] not in AGGREGATION_STAGE_ORDER
            or not isinstance(row["manifest_sha256"], str)
            or HEX64.fullmatch(row["manifest_sha256"]) is None
        ):
            raise ProtocolError("aggregation progress stage record is invalid")
        published.append(row)
    published_ids = tuple(row["stage_id"] for row in published)
    if published_ids != AGGREGATION_STAGE_ORDER[: len(published_ids)]:
        raise ProtocolError("aggregation progress stages are not the exact prefix")

    assignment_lists: dict[str, list[str]] = {}
    for field in (
        "sealed_assignments",
        "started_assignments",
        "leaseable_assignments",
        "pending_assignments",
    ):
        rows = progress[field]
        if (
            not isinstance(rows, list)
            or rows != sorted(rows)
            or len(rows) != len(set(rows))
            or any(
                not isinstance(assignment, str)
                or (
                    REPORT_RUN_ID.fullmatch(assignment) is None
                    and re.fullmatch(r"[EVFPBLRQ]-(?:s[12]|c[12]|a1)", assignment)
                    is None
                    and assignment not in (*MATERIALITY_REVIEWERS, "ma1")
                )
                for assignment in rows
            )
        ):
            raise ProtocolError(f"aggregation progress {field} is invalid")
        assignment_lists[field] = rows
    sealed = set(assignment_lists["sealed_assignments"])
    started = set(assignment_lists["started_assignments"])
    leaseable = set(assignment_lists["leaseable_assignments"])
    pending = set(assignment_lists["pending_assignments"])
    if (
        sealed & started
        or sealed & leaseable
        or started & leaseable
        or pending != started | leaseable
    ):
        raise ProtocolError("aggregation progress assignment partitions overlap or drift")

    final_digest = progress["final_aggregate_sha256"]
    terminal_digest = progress["terminal_failure_sha256"]
    if final_digest is not None and (
        not isinstance(final_digest, str) or HEX64.fullmatch(final_digest) is None
    ):
        raise ProtocolError("aggregation progress final digest is invalid")
    if terminal_digest is not None and (
        not isinstance(terminal_digest, str)
        or HEX64.fullmatch(terminal_digest) is None
    ):
        raise ProtocolError("aggregation progress terminal digest is invalid")
    if status == "WAITING":
        valid_state = (
            current_stage == "reports"
            and not published_ids
            and final_digest is None
            and terminal_digest is None
            and bool(pending)
        )
    elif status == "DERIVABLE":
        valid_state = (
            len(published_ids) < len(AGGREGATION_STAGE_ORDER)
            and current_stage == AGGREGATION_STAGE_ORDER[len(published_ids)]
            and final_digest is None
            and terminal_digest is None
            and not pending
        )
    elif status == "PUBLISHED":
        valid_state = (
            bool(published_ids)
            and published_ids[-1] != "final"
            and current_stage == published_ids[-1]
            and final_digest is None
            and terminal_digest is None
            and bool(pending)
        )
    elif status == "COMPLETE":
        valid_state = (
            published_ids == AGGREGATION_STAGE_ORDER
            and current_stage == "final"
            and final_digest is not None
            and terminal_digest is None
            and 154 <= len(sealed) <= 163
            and not pending
            and not started
            and not leaseable
        )
    else:
        blocked_index = AGGREGATION_STAGE_ORDER.index(current_stage)
        valid_state = (
            published_ids == AGGREGATION_STAGE_ORDER[:blocked_index]
            and final_digest is None
            and terminal_digest is not None
            and not pending
            and not started
            and not leaseable
        )
    if not valid_state:
        raise ProtocolError("aggregation progress status/topology is inconsistent")
    return progress


def aggregation_progress_document(
    *,
    state: str,
    current_stage: str,
    coordinator_actor_id: str,
    published_stages: list[dict[str, str]],
    attempts: dict[str, dict[str, Any]],
    leaseable_assignments: set[str],
    pending_assignments: set[str],
    final_aggregate_sha256: str | None = None,
    terminal_failure_sha256: str | None = None,
) -> dict[str, Any]:
    return validate_aggregation_progress({
        "schema_version": 1,
        "status": state,
        "current_stage": current_stage,
        "coordinator_actor_id": require_production_actor_id(
            coordinator_actor_id, "aggregation coordinator actor ID"
        ),
        "published_stages": published_stages,
        "sealed_assignments": sorted(
            assignment
            for assignment, attempt in attempts.items()
            if attempt["status"] == "SEALED"
        ),
        "started_assignments": sorted(
            assignment
            for assignment, attempt in attempts.items()
            if attempt["status"] == "STARTED"
        ),
        "leaseable_assignments": sorted(leaseable_assignments),
        "pending_assignments": sorted(pending_assignments),
        "final_aggregate_sha256": final_aggregate_sha256,
        "terminal_failure_sha256": terminal_failure_sha256,
    })


def advance_aggregation(
    static_root: Path,
    external_commitment_path: Path,
    coordinator_actor_id: str | None,
    *,
    publish: bool = True,
) -> dict[str, Any]:
    """Advance the deterministic runtime DAG to its first unmet prerequisite."""

    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        return _advance_aggregation_under_custody(
            root, commitment, coordinator_actor_id, publish=publish
        )


def _advance_aggregation_under_custody(
    static_root: Path,
    external_commitment_path: Path,
    coordinator_actor_id: str | None,
    *,
    publish: bool,
) -> dict[str, Any]:

    if type(publish) is not bool:
        raise ProtocolError("aggregation publish authority must be boolean")
    if coordinator_actor_id is not None:
        coordinator_actor_id = require_production_actor_id(
            coordinator_actor_id, "aggregation coordinator actor ID"
        )
    root, static_lock, reviewer_ids, review_evidence = (
        load_verified_static_bundle_with_review_evidence(
            static_root, external_commitment_path
        )
    )
    if coordinator_actor_id is not None:
        require_production_runtime_actor(
            coordinator_actor_id,
            "aggregation coordinator actor ID",
            reviewer_ids,
        )
    return _advance_aggregation_from_verified(
        root,
        static_lock,
        reviewer_ids,
        review_evidence,
        coordinator_actor_id,
        publish=publish,
    )


def _advance_aggregation_from_verified(
    root: Path,
    static_lock: dict[str, Any],
    reviewer_ids: frozenset[str],
    review_evidence: dict[str, Any],
    coordinator_actor_id: str | None,
    *,
    publish: bool,
) -> dict[str, Any]:
    """Advance using one already authenticated static/reviewer capture."""

    if type(publish) is not bool:
        raise ProtocolError("aggregation publish authority must be boolean")
    context = load_aggregation_static_context(
        root, static_lock, reviewer_ids, review_evidence
    )
    state_root = root / "runtime" / "state"
    if not state_root.is_dir() or state_root.is_symlink():
        raise ProtocolError("aggregation requires an initialized runtime/state")
    aggregation_root = state_root / "aggregation"
    published_stages: list[dict[str, str]] = []

    def require_no_terminal_before_wait() -> None:
        terminal_path = aggregation_root / AGGREGATION_TERMINAL_FAILURE
        if terminal_path.exists() or terminal_path.is_symlink():
            raise ProtocolError(
                "aggregation terminal failure exists before its sealed phase barrier"
            )

    def complete_stage(
        stage_id: str,
        files: dict[str, bytes],
        prerequisite_sha: str | None,
        prerequisite_assignments: set[str],
    ) -> str:
        expected_manifest = build_aggregation_stage_manifest(
            stage_id,
            files,
            static_lock_sha256=context["static_lock_sha256"],
            coordinator_actor_id=coordinator_actor_id,
            prerequisite_stage_sha256=prerequisite_sha,
            attempt_envelopes=sealed_attempt_envelopes(
                attempts, prerequisite_assignments
            ),
        )
        stage_path = (
            aggregation_root / "final"
            if stage_id == "final"
            else aggregation_root / "derived" / stage_id
        )
        if publish:
            manifest = publish_or_verify_aggregation_stage(
                aggregation_root,
                stage_id,
                files,
                static_lock_sha256=context["static_lock_sha256"],
                coordinator_actor_id=coordinator_actor_id,
                prerequisite_stage_sha256=prerequisite_sha,
                attempt_envelopes=sealed_attempt_envelopes(
                    attempts, prerequisite_assignments
                ),
            )
        elif (stage_path / "stage-manifest.json").exists():
            manifest = _validate_aggregation_stage_tree(
                stage_path, files, expected_manifest
            )
        else:
            raise AggregationStageDerivable(
                aggregation_progress_document(
                    state="DERIVABLE",
                    current_stage=stage_id,
                    coordinator_actor_id=coordinator_actor_id,
                    published_stages=published_stages,
                    attempts=attempts,
                    leaseable_assignments=set(),
                    pending_assignments=set(),
                )
            )
        digest = aggregation_stage_digest(manifest)
        expected_prefix = AGGREGATION_STAGE_ORDER[
            : AGGREGATION_STAGE_ORDER.index(stage_id) + 1
        ]
        committed_stages = validate_aggregation_directory_inventory(
            aggregation_root, require_final=stage_id == "final"
        )
        if (
            committed_stages[: len(expected_prefix)] != expected_prefix
            or (stage_id == "final" and committed_stages != expected_prefix)
        ):
            raise ProtocolError(
                f"aggregation stage publication is not the exact prefix through {stage_id}"
            )
        published_stages.append(
            {"stage_id": stage_id, "manifest_sha256": digest}
        )
        return digest

    def complete_terminal_failure(
        blocked_stage_id: str,
        prerequisite_sha: str | None,
        cumulative_assignments: set[str],
        failure_assignments: set[str],
    ) -> dict[str, Any]:
        expected = build_aggregation_terminal_failure(
            blocked_stage_id=blocked_stage_id,
            static_lock_sha256=context["static_lock_sha256"],
            coordinator_actor_id=coordinator_actor_id,
            prerequisite_stage_sha256=prerequisite_sha,
            attempts=attempts,
            cumulative_assignments=cumulative_assignments,
            failure_assignments=failure_assignments,
        )
        terminal_path = aggregation_root / AGGREGATION_TERMINAL_FAILURE
        if publish:
            terminal = publish_or_verify_aggregation_terminal_failure(
                aggregation_root, expected
            )
        elif terminal_path.exists() or terminal_path.is_symlink():
            terminal = validate_aggregation_terminal_failure(
                read_committed_json(
                    terminal_path, "aggregation terminal failure"
                )
            )
            if (
                terminal != expected
                or terminal_path.read_bytes() != canonical_json_bytes(expected)
            ):
                raise ProtocolError(
                    "aggregation terminal failure is not the exact rederivation"
                )
        else:
            raise AggregationStageDerivable(
                aggregation_progress_document(
                    state="DERIVABLE",
                    current_stage=blocked_stage_id,
                    coordinator_actor_id=coordinator_actor_id,
                    published_stages=published_stages,
                    attempts=attempts,
                    leaseable_assignments=set(),
                    pending_assignments=set(),
                )
            )
        expected_prefix = AGGREGATION_STAGE_ORDER[
            : AGGREGATION_STAGE_ORDER.index(blocked_stage_id)
        ]
        if validate_aggregation_directory_inventory(
            aggregation_root, require_final=False
        ) != expected_prefix:
            raise ProtocolError(
                "terminal failure does not follow the exact committed stage prefix"
            )
        return aggregation_progress_document(
            state="TERMINAL-FAILURE",
            current_stage=blocked_stage_id,
            coordinator_actor_id=coordinator_actor_id,
            published_stages=published_stages,
            attempts=attempts,
            leaseable_assignments=set(),
            pending_assignments=set(),
            terminal_failure_sha256=sha256(canonical_json_bytes(terminal)),
        )

    with operation_lock(state_root):
        claim_path = aggregation_root / AGGREGATION_COORDINATOR_CLAIM
        if claim_path.exists() or claim_path.is_symlink():
            claim = load_aggregation_coordinator_claim(
                state_root, context["static_lock_sha256"], reviewer_ids
            )
            if (
                coordinator_actor_id is not None
                and coordinator_actor_id != claim["coordinator_actor_id"]
            ):
                raise ProtocolError("aggregation coordinator identity drifted")
        else:
            if coordinator_actor_id is None:
                raise ProtocolError(
                    "aggregation coordinator identity is required before report leasing"
                )
            if not publish:
                raise ProtocolError(
                    "read-only aggregation status requires an existing coordinator claim"
                )
            if _authoritative_leases(
                state_root, production_reviewer_ids=reviewer_ids
            ):
                raise ProtocolError(
                    "aggregation coordinator must be claimed before every semantic lease"
                )
            claim = build_aggregation_coordinator_claim(
                coordinator_actor_id,
                context["static_lock_sha256"],
                reviewer_ids,
            )
        if publish:
            recover_exclusive_write_residues(state_root)
            if aggregation_root.exists():
                recover_private_aggregation_stages(aggregation_root)
            _write_or_validate_immutable(claim_path, claim)
        coordinator_actor_id = claim["coordinator_actor_id"]
        reserved_actor_ids = reviewer_ids | {coordinator_actor_id}
        attempts = _load_attempt_progress_locked(
            state_root, reserved_actor_ids, root
        )
        report_ids = {f"r{index:03d}" for index in range(1, 121)}
        report_sealed, report_started = exact_progress_partition(
            attempts,
            completed=set(),
            eligible=report_ids,
            label="report collection",
        )
        if report_sealed != report_ids:
            require_no_terminal_before_wait()
            if validate_aggregation_directory_inventory(
                aggregation_root, require_final=False
            ):
                raise ProtocolError(
                    "aggregation stages exist before report collection is complete"
                )
            return aggregation_progress_document(
                state="WAITING",
                current_stage="reports",
                coordinator_actor_id=coordinator_actor_id,
                published_stages=published_stages,
                attempts=attempts,
                leaseable_assignments=report_ids - set(attempts),
                pending_assignments=(report_ids - report_sealed) | report_started,
            )

        report_failures = aggregation_phase_failure_assignments(
            attempts, report_ids, report_phase=True
        )
        if report_failures:
            return complete_terminal_failure(
                "01-report-products", None, report_ids, report_failures
            )

        report_files, report_products = derive_report_products(context, attempts)
        stage_01_sha = complete_stage(
            "01-report-products", report_files, None, report_ids
        )
        scorer_ids = {f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS}
        scorer_sealed, scorer_started = exact_progress_partition(
            attempts,
            completed=report_ids,
            eligible=scorer_ids,
            label="scorer collection",
        )
        if scorer_sealed != scorer_ids:
            require_no_terminal_before_wait()
            return aggregation_progress_document(
                state="PUBLISHED",
                current_stage="01-report-products",
                coordinator_actor_id=coordinator_actor_id,
                published_stages=published_stages,
                attempts=attempts,
                leaseable_assignments=scorer_ids - set(attempts),
                pending_assignments=(scorer_ids - scorer_sealed) | scorer_started,
            )

        scorer_failures = aggregation_phase_failure_assignments(
            attempts, scorer_ids, report_phase=False
        )
        if scorer_failures:
            return complete_terminal_failure(
                "02-scorer-products",
                stage_01_sha,
                report_ids | scorer_ids,
                scorer_failures,
            )

        scorer_files, scorer_products = derive_scorer_products(
            context, attempts, report_products
        )
        cumulative = report_ids | scorer_ids
        stage_02_sha = complete_stage(
            "02-scorer-products",
            scorer_files,
            stage_01_sha,
            cumulative,
        )
        consistency_ids = {
            f"{mode}-{reviewer}"
            for mode in MODES
            for reviewer in CONSISTENCY_REVIEWERS
        }
        consistency_sealed, consistency_started = exact_progress_partition(
            attempts,
            completed=cumulative,
            eligible=consistency_ids,
            label="consistency collection",
        )
        if consistency_sealed != consistency_ids:
            require_no_terminal_before_wait()
            return aggregation_progress_document(
                state="PUBLISHED",
                current_stage="02-scorer-products",
                coordinator_actor_id=coordinator_actor_id,
                published_stages=published_stages,
                attempts=attempts,
                leaseable_assignments=consistency_ids - set(attempts),
                pending_assignments=(consistency_ids - consistency_sealed)
                | consistency_started,
            )

        consistency_failures = aggregation_phase_failure_assignments(
            attempts, consistency_ids, report_phase=False
        )
        if consistency_failures:
            return complete_terminal_failure(
                "03-consistency-products",
                stage_02_sha,
                cumulative | consistency_ids,
                consistency_failures,
            )

        consistency_files, consistency_products = derive_consistency_products(
            context, attempts, report_products, scorer_products
        )
        cumulative |= consistency_ids
        stage_03_sha = complete_stage(
            "03-consistency-products",
            consistency_files,
            stage_02_sha,
            cumulative,
        )
        adjudicator_ids = consistency_products["required_adjudicators"]
        adjudicator_sealed, adjudicator_started = exact_progress_partition(
            attempts,
            completed=cumulative,
            eligible=adjudicator_ids,
            label="mode adjudication collection",
        )
        if adjudicator_sealed != adjudicator_ids:
            require_no_terminal_before_wait()
            return aggregation_progress_document(
                state="PUBLISHED",
                current_stage="03-consistency-products",
                coordinator_actor_id=coordinator_actor_id,
                published_stages=published_stages,
                attempts=attempts,
                leaseable_assignments=adjudicator_ids - set(attempts),
                pending_assignments=(adjudicator_ids - adjudicator_sealed)
                | adjudicator_started,
            )

        adjudicator_failures = aggregation_phase_failure_assignments(
            attempts, adjudicator_ids, report_phase=False
        )
        if adjudicator_failures:
            return complete_terminal_failure(
                "04-score-products",
                stage_03_sha,
                cumulative | adjudicator_ids,
                adjudicator_failures,
            )

        score_files, score_products = derive_score_products(
            context,
            attempts,
            report_products,
            scorer_products,
            consistency_products,
        )
        cumulative |= adjudicator_ids
        stage_04_sha = complete_stage(
            "04-score-products", score_files, stage_03_sha, cumulative
        )
        materiality_ids = set(MATERIALITY_REVIEWERS)
        materiality_sealed, materiality_started = exact_progress_partition(
            attempts,
            completed=cumulative,
            eligible=materiality_ids,
            label="materiality review collection",
        )
        if materiality_sealed != materiality_ids:
            require_no_terminal_before_wait()
            return aggregation_progress_document(
                state="PUBLISHED",
                current_stage="04-score-products",
                coordinator_actor_id=coordinator_actor_id,
                published_stages=published_stages,
                attempts=attempts,
                leaseable_assignments=materiality_ids - set(attempts),
                pending_assignments=(materiality_ids - materiality_sealed)
                | materiality_started,
            )

        materiality_failures = aggregation_phase_failure_assignments(
            attempts, materiality_ids, report_phase=False
        )
        if materiality_failures:
            return complete_terminal_failure(
                "05-materiality-products",
                stage_04_sha,
                cumulative | materiality_ids,
                materiality_failures,
            )

        materiality_files, materiality_products = (
            derive_materiality_review_products(context, attempts, score_products)
        )
        cumulative |= materiality_ids
        stage_05_sha = complete_stage(
            "05-materiality-products",
            materiality_files,
            stage_04_sha,
            cumulative,
        )
        materiality_adjudicator_ids = (
            {"ma1"} if materiality_products["requires_adjudicator"] else set()
        )
        ma_sealed, ma_started = exact_progress_partition(
            attempts,
            completed=cumulative,
            eligible=materiality_adjudicator_ids,
            label="materiality adjudication collection",
        )
        if ma_sealed != materiality_adjudicator_ids:
            require_no_terminal_before_wait()
            return aggregation_progress_document(
                state="PUBLISHED",
                current_stage="05-materiality-products",
                coordinator_actor_id=coordinator_actor_id,
                published_stages=published_stages,
                attempts=attempts,
                leaseable_assignments=materiality_adjudicator_ids - set(attempts),
                pending_assignments=(materiality_adjudicator_ids - ma_sealed)
                | ma_started,
            )

        materiality_adjudicator_failures = aggregation_phase_failure_assignments(
            attempts, materiality_adjudicator_ids, report_phase=False
        )
        if materiality_adjudicator_failures:
            return complete_terminal_failure(
                "final",
                stage_05_sha,
                cumulative | materiality_adjudicator_ids,
                materiality_adjudicator_failures,
            )

        cumulative |= materiality_adjudicator_ids
        final_files, final_products = derive_final_aggregation_products(
            context,
            attempts,
            report_products,
            scorer_products,
            consistency_products,
            score_products,
            materiality_products,
            coordinator_actor_id,
        )
        complete_stage("final", final_files, stage_05_sha, cumulative)
        return aggregation_progress_document(
            state="COMPLETE",
            current_stage="final",
            coordinator_actor_id=coordinator_actor_id,
            published_stages=published_stages,
            attempts=attempts,
            leaseable_assignments=set(),
            pending_assignments=set(),
            final_aggregate_sha256=sha256(
                canonical_json_bytes(final_products["aggregate"])
            ),
        )


def aggregation_status(
    static_root: Path,
    external_commitment_path: Path,
) -> dict[str, Any]:
    """Report deterministic aggregation progress without publishing any bytes."""

    try:
        return advance_aggregation(
            static_root,
            external_commitment_path,
            None,
            publish=False,
        )
    except AggregationStageDerivable as state:
        return state.progress


def build_production_evaluator_launch(
    static_root: Path,
    external_commitment_path: Path,
    assignment_id: str,
) -> dict[str, Any]:
    """Return one already-derived authoritative evaluator launch."""

    evaluator_stage_location(assignment_id)
    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        try:
            progress = _advance_aggregation_under_custody(
                root, commitment, None, publish=False
            )
        except AggregationStageDerivable as state:
            progress = state.progress
        if assignment_id not in progress["leaseable_assignments"]:
            raise ProtocolError(
                f"evaluator assignment is not currently leaseable: {assignment_id}"
            )
        verified_root, _lock, _reviewer_ids = load_verified_static_bundle(
            root, commitment
        )
        _packet_path, _launch_path, _spec_path, _packet, launch = (
            load_authoritative_evaluator_material(
                verified_root,
                assignment_id,
                capability=_PRODUCTION_LEASE_CAPABILITY,
            )
        )
        return launch


def evaluator_stage_location(assignment_id: str) -> tuple[str, str, str]:
    require_safe_id(assignment_id, "evaluator assignment")
    if re.fullmatch(r"[EVFPBLRQ]-s[12]", assignment_id):
        return (
            "01-report-products",
            f"packets/scorers/{assignment_id}.json",
            f"launches/scorers/{assignment_id}.json",
        )
    match = re.fullmatch(r"([EVFPBLRQ])-c[12]", assignment_id)
    if match:
        mode = match.group(1)
        return (
            "02-scorer-products",
            f"packets/consistency/{mode}.json",
            f"launches/consistency/{assignment_id}.json",
        )
    match = re.fullmatch(r"([EVFPBLRQ])-a1", assignment_id)
    if match:
        mode = match.group(1)
        return (
            "03-consistency-products",
            f"packets/adjudication/{mode}.json",
            f"launches/adjudication/{assignment_id}.json",
        )
    if assignment_id in MATERIALITY_REVIEWERS:
        return (
            "04-score-products",
            "packets/materiality-review.json",
            f"launches/materiality/{assignment_id}.json",
        )
    if assignment_id == "ma1":
        return (
            "05-materiality-products",
            "packets/materiality-adjudication.json",
            "launches/materiality/ma1.json",
        )
    raise ProtocolError(f"unknown evaluator assignment: {assignment_id}")


def load_authoritative_evaluator_material(
    root: Path,
    assignment_id: str,
    *,
    capability: object | None = None,
    ready_documents: dict[str, Any] | None = None,
) -> tuple[Path, Path, Path, dict[str, Any], dict[str, Any]]:
    if capability is not _PRODUCTION_LEASE_CAPABILITY:
        raise ProtocolError(
            "evaluator stage material is available only through the assignment-only production route"
        )
    stage_id, packet_relative, launch_relative = evaluator_stage_location(
        assignment_id
    )
    aggregation_root = root / "runtime" / "state" / "aggregation"
    packet_path = aggregation_stage_file(
        aggregation_root, stage_id, packet_relative
    )
    launch_path = aggregation_stage_file(
        aggregation_root, stage_id, launch_relative
    )
    packet_bytes = packet_path.read_bytes()
    launch_bytes = launch_path.read_bytes()
    packet = strict_json_loads(packet_bytes, str(packet_path))
    launch = validate_launch_record(strict_json_loads(launch_bytes, str(launch_path)))
    documents = (
        ready_documents
        if ready_documents is not None
        else load_ready_generated_documents(root)
    )
    expected_launch, row = build_expected_evaluator_launch(
        root, documents, assignment_id, packet_bytes
    )
    if (
        launch != expected_launch
        or launch_bytes != canonical_json_bytes(expected_launch)
    ):
        raise ProtocolError(
            f"published evaluator launch is not the exact derivation: {assignment_id}"
        )
    validate_evaluator_packet_for_role(packet, row)
    spec_path = root / Path(*PurePosixPath(row["envelope_spec_path"]).parts)
    return packet_path, launch_path, spec_path, packet, launch


def acquire_evaluator_lease(
    static_root: Path,
    external_commitment_path: Path,
    assignment_id: str,
    agent_id: str,
) -> dict[str, Any]:
    """Lease one evaluator using only its assignment-owned staged material."""

    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        return _acquire_evaluator_lease_under_custody(
            root, commitment, assignment_id, agent_id
        )


def _acquire_evaluator_lease_under_custody(
    static_root: Path,
    external_commitment_path: Path,
    assignment_id: str,
    agent_id: str,
) -> dict[str, Any]:

    evaluator_stage_location(assignment_id)
    agent_id = require_production_actor_id(
        agent_id, "production evaluator agent ID"
    )
    root, static_lock, reviewer_ids, review_evidence = (
        load_verified_static_bundle_with_review_evidence(
            static_root, external_commitment_path
        )
    )
    claim = load_aggregation_coordinator_claim(
        root / "runtime" / "state",
        sha256(canonical_json_bytes(static_lock)),
        reviewer_ids,
    )
    reserved_actor_ids = reviewer_ids | {claim["coordinator_actor_id"]}
    require_production_runtime_actor(
        agent_id, "production evaluator agent ID", reserved_actor_ids
    )
    state_root = root / "runtime" / "state"
    with operation_lock(state_root):
        _write_or_validate_immutable(
            state_root / "aggregation" / AGGREGATION_COORDINATOR_CLAIM,
            claim,
        )
        lease_path = state_root / "slots" / assignment_id / "lease.json"
        recovering = lease_path.is_file() and not lease_path.is_symlink()
        if recovering:
            existing = validate_lease(
                read_committed_json(lease_path, "recovering evaluator lease")
            )
            if (
                existing["slot_id"] != assignment_id
                or existing["agent_id"] != agent_id
            ):
                raise LeaseAlreadyExists(
                    "evaluator assignment already belongs to a different lease"
                )
            recover_exclusive_write_residues(state_root)
            recovered_state = _verify_state_locked(
                state_root,
                production_reviewer_ids=reserved_actor_ids,
                production_static_root=root,
            )
            recovered_row = next(
                (
                    row
                    for row in recovered_state["slots"]
                    if row["slot_id"] == assignment_id
                ),
                None,
            )
            if recovered_row is None or recovered_row["status"] not in (
                "LEASE_INITIALIZING",
                "STARTED",
            ):
                raise LeaseAlreadyExists(
                    "evaluator lease is not in a recoverable pre-terminal state"
                )
    if not recovering:
        progress = _advance_aggregation_from_verified(
            root,
            static_lock,
            reviewer_ids,
            review_evidence,
            None,
            publish=True,
        )
        if assignment_id not in progress["leaseable_assignments"]:
            raise ProtocolError(
                f"evaluator assignment is not currently leaseable: {assignment_id}"
            )
    packet_path, launch_path, spec_path, _packet, launch = (
        load_authoritative_evaluator_material(
            root,
            assignment_id,
            capability=_PRODUCTION_LEASE_CAPABILITY,
        )
    )
    return acquire_lease(
        state_root,
        launch_path,
        agent_id,
        spec_path,
        Path(launch["output_root"]),
        packet_path,
        production_context=(root, reserved_actor_ids),
        production_capability=_PRODUCTION_LEASE_CAPABILITY,
    )


def acquire_report_lease(
    static_root: Path,
    external_commitment_path: Path,
    run_id: str,
    agent_id: str,
) -> dict[str, Any]:
    """Lease one report using only its authenticated static run identity."""

    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        return _acquire_report_lease_under_custody(
            root, commitment, run_id, agent_id
        )


def _acquire_report_lease_under_custody(
    static_root: Path,
    external_commitment_path: Path,
    run_id: str,
    agent_id: str,
) -> dict[str, Any]:

    if not isinstance(run_id, str) or REPORT_RUN_ID.fullmatch(run_id) is None:
        raise ProtocolError("report lease run ID is invalid")
    agent_id = require_production_actor_id(
        agent_id, "production report agent ID"
    )
    root, static_lock, reviewer_ids = load_verified_static_bundle(
        static_root, external_commitment_path
    )
    claim = load_aggregation_coordinator_claim(
        root / "runtime" / "state",
        sha256(canonical_json_bytes(static_lock)),
        reviewer_ids,
    )
    reserved_actor_ids = reviewer_ids | {claim["coordinator_actor_id"]}
    require_production_runtime_actor(
        agent_id, "production report agent ID", reserved_actor_ids
    )
    state_root = root / "runtime" / "state"
    with operation_lock(state_root):
        _write_or_validate_immutable(
            state_root / "aggregation" / AGGREGATION_COORDINATOR_CLAIM,
            claim,
        )
    documents = load_ready_generated_documents(root)
    launch = next(
        item for item in documents["report-launch-records"] if item["run_id"] == run_id
    )
    launch_path = (
        root / "static" / "generated" / "launch-records" / f"{run_id}.json"
    )
    plan_path = (
        root
        / "static"
        / "generated"
        / "report-input-plans"
        / f"{run_id}.json"
    )
    spec_path = (
        root
        / "static"
        / "envelope-specs"
        / f"report-{launch['mode']}.json"
    )
    return acquire_lease(
        state_root,
        launch_path,
        agent_id,
        spec_path,
        Path(launch["output_root"]),
        plan_path,
        production_context=(root, reserved_actor_ids),
        production_capability=_PRODUCTION_LEASE_CAPABILITY,
    )


def seal_production_attempt(
    static_root: Path,
    external_commitment_path: Path,
    slot_id: str,
    lease_token: str,
    agent_id: str,
    final_response: bytes | OversizedFinalResponse | None,
    process_disposition: str,
    process_exit_code: int | None,
    metadata: dict[str, Any],
) -> dict[str, Any]:
    """Seal using the attempt root already authenticated by the lease ledger."""

    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        return _seal_production_attempt_under_custody(
            root,
            commitment,
            slot_id,
            lease_token,
            agent_id,
            final_response,
            process_disposition,
            process_exit_code,
            metadata,
        )


def _seal_production_attempt_under_custody(
    static_root: Path,
    external_commitment_path: Path,
    slot_id: str,
    lease_token: str,
    agent_id: str,
    final_response: bytes | OversizedFinalResponse | None,
    process_disposition: str,
    process_exit_code: int | None,
    metadata: dict[str, Any],
) -> dict[str, Any]:

    slot_id = require_safe_id(slot_id, "slot ID")
    agent_id = require_production_actor_id(
        agent_id, "production seal agent ID"
    )
    if not isinstance(lease_token, str) or HEX64.fullmatch(lease_token) is None:
        raise ProtocolError("invalid lease token")
    if not isinstance(metadata, dict):
        raise ProtocolError("coordinator metadata must be an object")
    require_safe_id(process_disposition, "process disposition")
    if process_exit_code is not None and type(process_exit_code) is not int:
        raise ProtocolError("process exit code must be an integer or null")
    describe_final_response(final_response)
    canonical_json_bytes(metadata)
    root, static_lock, reviewer_ids = load_verified_static_bundle(
        static_root, external_commitment_path
    )
    state_root = root / "runtime" / "state"
    claim = load_aggregation_coordinator_claim(
        state_root,
        sha256(canonical_json_bytes(static_lock)),
        reviewer_ids,
    )
    reserved_actor_ids = reviewer_ids | {claim["coordinator_actor_id"]}
    require_production_runtime_actor(
        agent_id, "production seal agent ID", reserved_actor_ids
    )
    with operation_lock(state_root):
        lease_path = state_root / "slots" / slot_id / "lease.json"
        lease = validate_lease(
            read_committed_json(lease_path, "production seal lease")
        )
        require_production_runtime_actor(
            lease["agent_id"],
            "persisted production lease agent ID",
            reserved_actor_ids,
        )
        if lease["slot_id"] != slot_id:
            raise ProtocolError("production seal slot/lease mismatch")
        attempt_root = Path(lease["attempt_root"])
    return seal_attempt(
        state_root,
        slot_id,
        lease_token,
        agent_id,
        attempt_root,
        final_response,
        process_disposition,
        process_exit_code,
        metadata,
        production_context=(root, reserved_actor_ids),
        production_capability=_PRODUCTION_LEASE_CAPABILITY,
    )


def verify_production_state(
    static_root: Path, external_commitment_path: Path
) -> dict[str, Any]:
    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        return _verify_production_state_under_custody(root, commitment)


def _verify_production_state_under_custody(
    static_root: Path, external_commitment_path: Path
) -> dict[str, Any]:
    root, static_lock, reviewer_ids = load_verified_static_bundle(
        static_root, external_commitment_path
    )
    state_root = root / "runtime" / "state"
    claim = load_aggregation_coordinator_claim(
        state_root,
        sha256(canonical_json_bytes(static_lock)),
        reviewer_ids,
    )
    with operation_lock(state_root):
        return _verify_state_locked(
            state_root,
            production_reviewer_ids=reviewer_ids
            | {claim["coordinator_actor_id"]},
            production_static_root=root,
        )


def rederive_complete_aggregation_from_verified(
    root: Path,
    static_lock: dict[str, Any],
    reviewer_ids: frozenset[str],
    review_evidence: dict[str, Any],
) -> dict[str, Any]:
    """Rebuild and byte-compare the entire immutable stage chain."""

    terminal_path = (
        root
        / "runtime"
        / "state"
        / "aggregation"
        / AGGREGATION_TERMINAL_FAILURE
    )
    if terminal_path.exists() or terminal_path.is_symlink():
        progress = _advance_aggregation_from_verified(
            root,
            static_lock,
            reviewer_ids,
            review_evidence,
            None,
            publish=False,
        )
        if progress["status"] != "TERMINAL-FAILURE":
            raise ProtocolError("aggregation terminal outcome did not rederive")
        raise ProtocolError(
            "aggregation ended in an authenticated terminal error: "
            f"{progress['current_stage']}/"
            f"{progress['terminal_failure_sha256']}"
        )

    context = load_aggregation_static_context(
        root, static_lock, reviewer_ids, review_evidence
    )
    aggregation_root = root / "runtime" / "state" / "aggregation"
    validate_aggregation_directory_inventory(
        aggregation_root, require_final=True
    )
    claim = load_aggregation_coordinator_claim(
        root / "runtime" / "state",
        context["static_lock_sha256"],
        reviewer_ids,
    )
    coordinator_actor_id = claim["coordinator_actor_id"]
    reserved_actor_ids = reviewer_ids | {coordinator_actor_id}
    attempts = load_canonical_attempt_inventory(root, reserved_actor_ids)
    first_manifest_path = (
        aggregation_root
        / "derived"
        / "01-report-products"
        / "stage-manifest.json"
    )
    first_manifest = read_committed_json(
        first_manifest_path, "Stage 01 manifest"
    )
    if first_manifest.get("coordinator_actor_id") != coordinator_actor_id:
        raise ProtocolError("Stage 01 coordinator does not equal the immutable claim")

    def validate_stage(
        stage_id: str,
        files: dict[str, bytes],
        prerequisite_sha: str | None,
        prerequisite_assignments: set[str],
    ) -> str:
        expected = build_aggregation_stage_manifest(
            stage_id,
            files,
            static_lock_sha256=context["static_lock_sha256"],
            coordinator_actor_id=coordinator_actor_id,
            prerequisite_stage_sha256=prerequisite_sha,
            attempt_envelopes=sealed_attempt_envelopes(
                attempts, prerequisite_assignments
            ),
        )
        stage_root = (
            aggregation_root / "final"
            if stage_id == "final"
            else aggregation_root / "derived" / stage_id
        )
        manifest = _validate_aggregation_stage_tree(stage_root, files, expected)
        return aggregation_stage_digest(manifest)

    report_ids = {f"r{index:03d}" for index in range(1, 121)}
    report_files, report_products = derive_report_products(context, attempts)
    stage_01_sha = validate_stage(
        "01-report-products", report_files, None, report_ids
    )
    scorer_ids = {f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS}
    scorer_files, scorer_products = derive_scorer_products(
        context, attempts, report_products
    )
    cumulative = report_ids | scorer_ids
    stage_02_sha = validate_stage(
        "02-scorer-products", scorer_files, stage_01_sha, cumulative
    )
    consistency_ids = {
        f"{mode}-{reviewer}"
        for mode in MODES
        for reviewer in CONSISTENCY_REVIEWERS
    }
    consistency_files, consistency_products = derive_consistency_products(
        context, attempts, report_products, scorer_products
    )
    cumulative |= consistency_ids
    stage_03_sha = validate_stage(
        "03-consistency-products",
        consistency_files,
        stage_02_sha,
        cumulative,
    )
    score_files, score_products = derive_score_products(
        context,
        attempts,
        report_products,
        scorer_products,
        consistency_products,
    )
    cumulative |= consistency_products["required_adjudicators"]
    stage_04_sha = validate_stage(
        "04-score-products", score_files, stage_03_sha, cumulative
    )
    materiality_files, materiality_products = derive_materiality_review_products(
        context, attempts, score_products
    )
    cumulative |= set(MATERIALITY_REVIEWERS)
    stage_05_sha = validate_stage(
        "05-materiality-products",
        materiality_files,
        stage_04_sha,
        cumulative,
    )
    if materiality_products["requires_adjudicator"]:
        cumulative.add("ma1")
    final_files, final_products = derive_final_aggregation_products(
        context,
        attempts,
        report_products,
        scorer_products,
        consistency_products,
        score_products,
        materiality_products,
        coordinator_actor_id,
    )
    validate_stage("final", final_files, stage_05_sha, cumulative)
    return final_products


def attempt_output_json(attempt: dict[str, Any], label: str) -> Any:
    data = attempt["primary_bytes"]
    if not isinstance(data, bytes):
        raise ProtocolError(f"{label} lacks canonical primary output bytes")
    return strict_json_loads(data, label)


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


def _derive_aggregate_context_from_verified(
    root: Path,
    static_lock: dict[str, Any],
    production_reviewer_ids: frozenset[str],
    authenticated_review_evidence: dict[str, Any],
) -> dict[str, Any]:
    """Derive every gate input from one coherently verified static context."""

    return rederive_complete_aggregation_from_verified(
        root,
        static_lock,
        production_reviewer_ids,
        authenticated_review_evidence,
    )["aggregate"]



def derive_aggregate_context(
    static_root: Path, external_commitment_path: Path | None = None
) -> dict[str, Any]:
    """Verify once, then derive every gate input from that coherent capture."""

    with production_custody_lock(
        static_root, external_commitment_path
    ) as (root, commitment):
        return _derive_aggregate_context_under_custody(root, commitment)


def _derive_aggregate_context_under_custody(
    static_root: Path, external_commitment_path: Path
) -> dict[str, Any]:

    root, static_lock, reviewer_ids, review_evidence = (
        load_verified_static_bundle_with_review_evidence(
            static_root, external_commitment_path
        )
    )
    return _derive_aggregate_context_from_verified(
        root, static_lock, reviewer_ids, review_evidence
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
        "schemas/aggregation-coordinator-claim.schema.json",
        "schemas/aggregation-progress.schema.json",
        "schemas/aggregation-rules.schema.json",
        "schemas/aggregation-stage-manifest.schema.json",
        "schemas/aggregation-terminal-failure.schema.json",
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
    clean_consistency_packet = build_consistency_packet(
        clean_first,
        clean_second,
        score_input_first,
        score_input_second,
        synthetic_atoms,
        synthetic_rules,
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
        adjudication,
    )
    final_by_label = {report["label"]: report for report in final_score["reports"]}
    assert final_by_label["B"]["hard_errors"] == ["GH1"]
    assert final_by_label["C"]["global_defects"] == []
    assert len(final_by_label["D"]["novel_findings"]) == 1
    assert final_by_label["D"]["novel_findings"][0]["classification"] == "VALID_NEW_FINDING"
    stale_consistency_first = copy.deepcopy(consistency_first)
    stale_consistency_first["challenges"].append(
        {
            "label": "A",
            "field": "atom:E1",
            "proposed_decision": "PASS",
            "evidence": "A distinct valid challenge changes the adjudication packet.",
        }
    )
    stale_packet = build_adjudication_packet(
        first,
        second,
        score_input_first,
        score_input_second,
        stale_consistency_first,
        consistency_second,
        synthetic_atoms,
        synthetic_rules,
    )
    try:
        validate_adjudication(adjudication, stale_packet)
    except ProtocolError:
        pass
    else:
        raise AssertionError("stale adjudication survived a consistency-input change")
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
    for bad_json in (
        '{"a":1,"a":2}',
        '{"a":NaN}',
        '{"a":1e9999}',
        '{"evidence":"\\ud800"}',
    ):
        try:
            strict_json_loads(bad_json, "synthetic strict JSON")
        except ProtocolError:
            pass
        else:
            raise AssertionError("non-strict JSON was accepted")
    try:
        canonical_json_bytes({"evidence": "\ud800"})
    except ProtocolError:
        pass
    else:
        raise AssertionError("canonical JSON accepted an unpaired surrogate")
    deeply_nested_json = "[" * 10000 + "0" + "]" * 10000
    try:
        strict_json_loads(deeply_nested_json, "synthetic deeply nested JSON")
    except ProtocolError as error:
        if "nesting limit" not in str(error):
            raise AssertionError("deep JSON failed for the wrong reason") from error
    else:
        raise AssertionError("deeply nested JSON bypassed the bounded parser")
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
    ready_gates = {
        **copy.deepcopy(gates),
        "status": "READY",
        "manifest_version": DIAGNOSTIC_CONTRACT_VERSIONS["READY"],
    }
    ready_inventory = {
        **copy.deepcopy(inventory),
        "status": "READY",
        "inventory_version": DIAGNOSTIC_CONTRACT_VERSIONS["READY"],
    }
    validate_root_inventory(ready_inventory, "READY")
    validate_gate_manifest(ready_gates, ready_inventory, "READY")
    for crossed_inventory, expected_status in (
        ({**copy.deepcopy(inventory), "status": "READY"}, "READY"),
        (
            {
                **copy.deepcopy(ready_inventory),
                "status": "DRAFT",
            },
            "DRAFT",
        ),
    ):
        try:
            validate_root_inventory(crossed_inventory, expected_status)
        except ProtocolError:
            pass
        else:
            raise AssertionError("a crossed root-inventory status/version pair was accepted")
    crossed_gates = {**copy.deepcopy(gates), "status": "READY"}
    try:
        validate_gate_manifest(crossed_gates, ready_inventory, "READY")
    except ProtocolError:
        pass
    else:
        raise AssertionError("a crossed gate-manifest status/version pair was accepted")
    try:
        validate_root_inventory(inventory, "UNKNOWN")
    except ProtocolError:
        pass
    else:
        raise AssertionError("an unknown operational-contract status was accepted")
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
        mkdir_recovery_target = temporary_root / "durable-mkdir-recovery"
        original_fsync_directory = globals()["fsync_directory"]
        mkdir_parent_faults = 0

        def fail_new_directory_parent_fsync(path: Path) -> None:
            nonlocal mkdir_parent_faults
            if (
                Path(path) == mkdir_recovery_target.parent
                and mkdir_recovery_target.is_dir()
                and mkdir_parent_faults == 0
            ):
                mkdir_parent_faults += 1
                raise OSError("synthetic mkdir parent-fsync failure")
            original_fsync_directory(path)

        globals()["fsync_directory"] = fail_new_directory_parent_fsync
        try:
            try:
                durable_mkdir(mkdir_recovery_target)
            except OSError:
                pass
            else:
                raise AssertionError("durable mkdir parent-fsync fault was swallowed")
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if mkdir_parent_faults != 1 or not mkdir_recovery_target.is_dir():
            raise AssertionError("durable mkdir fault did not leave a visible directory")
        mkdir_retry_fsyncs: list[Path] = []

        def record_mkdir_retry_fsync(path: Path) -> None:
            mkdir_retry_fsyncs.append(Path(path))
            original_fsync_directory(path)

        globals()["fsync_directory"] = record_mkdir_retry_fsync
        try:
            durable_mkdir(mkdir_recovery_target)
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if (
            mkdir_recovery_target not in mkdir_retry_fsyncs
            or mkdir_recovery_target.parent not in mkdir_retry_fsyncs
        ):
            raise AssertionError(
                "durable mkdir retry did not repair the visible directory link"
            )
        real_directory_chain = temporary_root / "real-directory-chain"
        (real_directory_chain / "child").mkdir(parents=True)
        symlinked_directory_chain = temporary_root / "symlinked-directory-chain"
        symlinked_directory_chain.symlink_to(
            real_directory_chain, target_is_directory=True
        )
        try:
            durable_mkdir(symlinked_directory_chain / "child")
        except ProtocolError:
            pass
        else:
            raise AssertionError("durable mkdir accepted a symlinked ancestor")
        bounded_fifo = temporary_root / "bounded-input-fifo"
        os.mkfifo(bounded_fifo)
        try:
            read_bounded_file_prefix(
                bounded_fifo,
                MAX_ENVELOPE_CAPTURE_BYTES,
                "synthetic bounded FIFO",
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("bounded file capture blocked on or accepted a FIFO")
        lock_fifo_state = temporary_root / "lock-fifo-state"
        lock_fifo_state.mkdir()
        os.mkfifo(lock_fifo_state / ".protocol.lock")
        try:
            verify_state(
                lock_fifo_state,
                test_capability=_SYNTHETIC_TEST_CAPABILITY,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("protocol state accepted a FIFO lock ledger")

        inventory_state = temporary_root / "exact-inventory-state"
        inventory_state.mkdir()
        verify_state(
            inventory_state,
            test_capability=_SYNTHETIC_TEST_CAPABILITY,
        )
        rogue_agent_directory = inventory_state / "agents" / "rogue-empty-agent"
        rogue_agent_directory.mkdir(parents=True)
        try:
            verify_state(
                inventory_state,
                test_capability=_SYNTHETIC_TEST_CAPABILITY,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("unreferenced empty agent claim directory was accepted")
        rogue_agent_directory.rmdir()
        rogue_agent_directory.parent.rmdir()

        objects_parent = inventory_state / "objects"
        objects_parent.write_bytes(b"not a directory\n")
        try:
            verify_state(
                inventory_state,
                test_capability=_SYNTHETIC_TEST_CAPABILITY,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("regular-file objects parent was accepted")
        objects_parent.unlink()
        objects_parent.symlink_to("missing-objects-parent")
        try:
            verify_state(
                inventory_state,
                test_capability=_SYNTHETIC_TEST_CAPABILITY,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("dangling-symlink objects parent was accepted")
        objects_parent.unlink()
        (objects_parent / "sha256").mkdir(parents=True)
        (objects_parent / "rogue-sibling").touch()
        try:
            verify_state(
                inventory_state,
                test_capability=_SYNTHETIC_TEST_CAPABILITY,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("objects parent with an unexpected sibling was accepted")

        fifo_swap_output = temporary_root / "fifo-swap-output"
        fifo_swap_output.mkdir()
        fifo_swap_target = fifo_swap_output / "swap-target.txt"
        fifo_swap_target.write_bytes(b"regular before stable open\n")
        original_os_open = os.open
        fifo_swap_fired = False

        def fifo_swapping_open(
            path: str | bytes | os.PathLike[str] | os.PathLike[bytes],
            flags: int,
            mode: int = 0o777,
            *,
            dir_fd: int | None = None,
        ) -> int:
            nonlocal fifo_swap_fired
            if path == "swap-target.txt" and dir_fd is not None:
                if not flags & getattr(os, "O_NONBLOCK", 0):
                    raise AssertionError(
                        "stable output open omitted the nonblocking race defense"
                    )
                fifo_swap_fired = True
                os.rename(
                    "swap-target.txt",
                    "displaced-regular.txt",
                    src_dir_fd=dir_fd,
                    dst_dir_fd=dir_fd,
                )
                os.mkfifo("swap-target.txt", dir_fd=dir_fd)
            return original_os_open(path, flags, mode, dir_fd=dir_fd)

        os.open = fifo_swapping_open
        try:
            try:
                scan_output(fifo_swap_output, MAX_ENVELOPE_CAPTURE_BYTES)
            except ProtocolError as error:
                if "changed during stable open" not in str(error):
                    raise AssertionError(
                        "regular-to-FIFO swap failed for the wrong reason"
                    ) from error
            else:
                raise AssertionError("regular-to-FIFO swap was accepted")
        finally:
            os.open = original_os_open
        if not fifo_swap_fired:
            raise AssertionError("regular-to-FIFO stable-open race did not execute")
        custody_root = temporary_root / "custody-root"
        custody_displaced = temporary_root / "custody-root-displaced"
        custody_commitment = temporary_root / "custody-commitment.json"
        custody_root.mkdir()
        custody_commitment.write_text("{}\n", encoding="utf-8")
        try:
            try:
                with production_custody_lock(
                    custody_root, custody_commitment
                ):
                    custody_root.rename(custody_displaced)
                    custody_root.mkdir()
                    raise AggregationStageDerivable(
                        {"current_stage": "synthetic-custody-stage"}
                    )
            except ProtocolError as error:
                if "custody identity changed" not in str(error):
                    raise AssertionError(
                        "exceptional custody drift failed for the wrong reason"
                    ) from error
            else:
                raise AssertionError(
                    "exceptional operation bypassed the closing custody check"
                )
        finally:
            if custody_root.exists():
                shutil.rmtree(custody_root)
            if custody_displaced.exists():
                custody_displaced.rename(custody_root)
        for alias in (".", "a//b", "a/./b", "a\\b"):
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
        mock_lock = {"schema_version": 2, "status": "STATIC-LOCKED"}
        mock_lock_sha256 = sha256(canonical_json_bytes(mock_lock))
        (mock_bundle / "STATIC-LOCK.json").write_bytes(
            canonical_json_bytes(mock_lock)
        )
        commitment_path = temporary_root / "external-static-commitment.json"
        expected_commitment = {
            "mock_external_commitment": True,
            "static_lock_sha256": mock_lock_sha256,
        }
        commitment_path.write_bytes(canonical_json_bytes(expected_commitment))
        wrong_commitment_path = temporary_root / "wrong-external-static-commitment.json"
        wrong_commitment_path.write_bytes(
            canonical_json_bytes(
                {
                    "mock_external_commitment": False,
                    "static_lock_sha256": mock_lock_sha256,
                }
            )
        )
        mock_reviewer_id_list = [
            f"locked-reviewer-{index:04d}" for index in range(1, 12)
        ]
        mock_reviewer_ids = frozenset(mock_reviewer_id_list)
        mock_source_records: list[dict[str, Any]] = []
        for index, (name, review_kind) in enumerate(SOURCE_REVIEW_KINDS.items()):
            receipt = {
                "status": "PASS",
                "review_kind": review_kind,
                "actor": {"identity": mock_reviewer_id_list[index]},
            }
            mock_source_records.append(
                {
                    "name": name,
                    "receipt_sha256": sha256(canonical_json_bytes(receipt)),
                    "receipt": receipt,
                }
            )
        mock_snapshot_records: list[dict[str, Any]] = []
        for index, hook_id in enumerate(SNAPSHOT_REVIEW_HOOK_IDS, start=3):
            receipt = {
                "status": "PASS",
                "phase": "SNAPSHOT_REVIEW",
                "hook_id": hook_id,
                "actor": {"identity": mock_reviewer_id_list[index]},
            }
            mock_snapshot_records.append(
                {
                    "hook_id": hook_id,
                    "receipt_sha256": sha256(canonical_json_bytes(receipt)),
                    "receipt": receipt,
                }
            )
        mock_review_evidence = {
            "schema_version": 1,
            "status": "AUTHENTICATED",
            "algorithm": AUTHENTICATED_REVIEW_EVIDENCE_ALGORITHM,
            "bundle_kind": "PRODUCTION",
            "static_lock_sha256": mock_lock_sha256,
            "source_review_receipts": mock_source_records,
            "snapshot_review_receipts": mock_snapshot_records,
        }
        mock_review_evidence_to_return = mock_review_evidence
        post_verify_reviewer_resolver_calls = 0

        def mock_trusted_integration() -> dict[str, Any]:
            def mock_verify_static_with_review_evidence(
                root: Path,
                *,
                expected_bundle_kind: str,
                expected_external_commitment: Any,
            ) -> tuple[dict[str, Any], frozenset[str], dict[str, Any]]:
                if (
                    root != mock_bundle
                    or expected_bundle_kind != "PRODUCTION"
                    or expected_external_commitment != expected_commitment
                ):
                    raise ProtocolError("mock external commitment mismatch")
                return (
                    mock_lock,
                    mock_reviewer_ids,
                    mock_review_evidence_to_return,
                )

            def forbidden_post_verify_reviewer_resolver(*_args: Any) -> frozenset[str]:
                nonlocal post_verify_reviewer_resolver_calls
                post_verify_reviewer_resolver_calls += 1
                raise AssertionError(
                    "protocol reopened reviewer receipts after static verification"
                )

            return {
                "verify_static_with_review_evidence": (
                    mock_verify_static_with_review_evidence
                ),
                "locked_reviewer_actor_ids": forbidden_post_verify_reviewer_resolver,
            }

        saved_trusted_integration = globals()["trusted_integration_module"]
        globals()["trusted_integration_module"] = mock_trusted_integration
        try:
            (
                loaded_root,
                _mock_lock,
                loaded_reviewer_ids,
                loaded_review_evidence,
            ) = load_verified_static_bundle_with_review_evidence(
                mock_bundle, commitment_path
            )
            assert loaded_root == mock_bundle
            assert loaded_reviewer_ids == mock_reviewer_ids
            assert loaded_review_evidence == mock_review_evidence
            wrong_lock_evidence = copy.deepcopy(mock_review_evidence)
            wrong_lock_evidence["static_lock_sha256"] = "0" * 64
            mock_review_evidence_to_return = wrong_lock_evidence
            try:
                load_verified_static_bundle_with_review_evidence(
                    mock_bundle, commitment_path
                )
            except ProtocolError:
                pass
            else:
                raise AssertionError(
                    "review evidence from a different static lock was accepted"
                )
            finally:
                mock_review_evidence_to_return = mock_review_evidence
            evidence_mutations: list[tuple[str, dict[str, Any]]] = []
            missing_evidence = copy.deepcopy(mock_review_evidence)
            missing_evidence["source_review_receipts"].pop()
            evidence_mutations.append(("missing source receipt", missing_evidence))
            extra_evidence = copy.deepcopy(mock_review_evidence)
            extra_evidence["snapshot_review_receipts"].append(
                copy.deepcopy(extra_evidence["snapshot_review_receipts"][-1])
            )
            evidence_mutations.append(("extra snapshot receipt", extra_evidence))
            wrong_hash_evidence = copy.deepcopy(mock_review_evidence)
            wrong_hash_evidence["source_review_receipts"][0]["receipt_sha256"] = "0" * 64
            evidence_mutations.append(("wrong receipt hash", wrong_hash_evidence))
            nonpass_evidence = copy.deepcopy(mock_review_evidence)
            nonpass_receipt = nonpass_evidence["source_review_receipts"][0]["receipt"]
            nonpass_receipt["status"] = "FAIL"
            nonpass_evidence["source_review_receipts"][0]["receipt_sha256"] = sha256(
                canonical_json_bytes(nonpass_receipt)
            )
            evidence_mutations.append(("non-PASS source receipt", nonpass_evidence))
            duplicate_actor_evidence = copy.deepcopy(mock_review_evidence)
            duplicate_receipt = duplicate_actor_evidence["snapshot_review_receipts"][0][
                "receipt"
            ]
            duplicate_receipt["actor"]["identity"] = mock_reviewer_id_list[0]
            duplicate_actor_evidence["snapshot_review_receipts"][0][
                "receipt_sha256"
            ] = sha256(canonical_json_bytes(duplicate_receipt))
            evidence_mutations.append(("duplicate reviewer actor", duplicate_actor_evidence))
            for label, mutated_evidence in evidence_mutations:
                try:
                    validate_authenticated_review_evidence(
                        mutated_evidence, mock_reviewer_ids
                    )
                except ProtocolError:
                    pass
                else:
                    raise AssertionError(
                        f"authenticated review evidence accepted {label}"
                    )
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
        validate_envelope_spec(inventory_spec)
        reserved_output_spec = copy.deepcopy(inventory_spec)
        reserved_output_spec["files"][0]["path"] = (
            ENCODED_OUTPUT_PATH_PREFIX + "reserved"
        )
        try:
            validate_envelope_spec(reserved_output_spec)
        except ProtocolError:
            pass
        else:
            raise AssertionError("reserved encoded-output namespace was declared")
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
        (evaluator_input / "undeclared.txt").unlink()
        (evaluator_input / "undeclared-empty-directory").mkdir()
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
            raise AssertionError("undeclared evaluator input directory was accepted")
        atomic_aggregation = temporary_root / "atomic-aggregation"
        atomic_files = {"nested/value.json": canonical_json_bytes({"value": 1})}
        original_directory_publish = globals()["_publish_directory_no_replace"]

        def fail_before_directory_publish(_stage: Path, _output: Path) -> None:
            raise InjectedFault("synthetic prepublication stage failure")

        globals()["_publish_directory_no_replace"] = fail_before_directory_publish
        try:
            try:
                publish_or_verify_aggregation_stage(
                    atomic_aggregation,
                    "01-report-products",
                    atomic_files,
                    static_lock_sha256="a" * 64,
                    coordinator_actor_id="synthetic-runtime-coordinator-0001",
                    prerequisite_stage_sha256=None,
                    attempt_envelopes={},
                )
            except InjectedFault:
                pass
            else:
                raise AssertionError("prepublication aggregation-stage fault did not fire")
        finally:
            globals()["_publish_directory_no_replace"] = original_directory_publish
        if any(atomic_aggregation.rglob(f"{AGGREGATION_PENDING_STAGE_PREFIX}*")):
            raise AssertionError("failed aggregation publication left a pending tree")
        atomic_manifest = publish_or_verify_aggregation_stage(
            atomic_aggregation,
            "01-report-products",
            atomic_files,
            static_lock_sha256="a" * 64,
            coordinator_actor_id="synthetic-runtime-coordinator-0001",
            prerequisite_stage_sha256=None,
            attempt_envelopes={},
        )
        if publish_or_verify_aggregation_stage(
            atomic_aggregation,
            "01-report-products",
            atomic_files,
            static_lock_sha256="a" * 64,
            coordinator_actor_id="synthetic-runtime-coordinator-0001",
            prerequisite_stage_sha256=None,
            attempt_envelopes={},
        ) != atomic_manifest:
            raise AssertionError("aggregation stage retry was not idempotent")
        atomic_stage_root = atomic_aggregation / "derived" / "01-report-products"
        if stat.S_IMODE(atomic_stage_root.lstat().st_mode) != 0o500 or any(
            stat.S_IMODE(path.lstat().st_mode) != (0o500 if path.is_dir() else 0o400)
            for path in atomic_stage_root.rglob("*")
        ):
            raise AssertionError("committed aggregation stage modes are not immutable")

        durability_aggregation = temporary_root / "durability-aggregation"
        durability_stage_root = (
            durability_aggregation / "derived" / "01-report-products"
        )
        durability_stage_parent = durability_stage_root.parent
        original_fsync_directory = globals()["fsync_directory"]
        failed_stage_parent_fsyncs = 0

        def fail_published_stage_parent_fsync(path: Path) -> None:
            nonlocal failed_stage_parent_fsyncs
            if (
                Path(path) == durability_stage_parent
                and path_entry_exists(durability_stage_root)
            ):
                failed_stage_parent_fsyncs += 1
                raise OSError("synthetic postpublication stage parent fsync failure")
            original_fsync_directory(path)

        globals()["fsync_directory"] = fail_published_stage_parent_fsync
        try:
            try:
                publish_or_verify_aggregation_stage(
                    durability_aggregation,
                    "01-report-products",
                    atomic_files,
                    static_lock_sha256="a" * 64,
                    coordinator_actor_id="synthetic-runtime-coordinator-0001",
                    prerequisite_stage_sha256=None,
                    attempt_envelopes={},
                )
            except OSError:
                pass
            else:
                raise AssertionError(
                    "exhausted stage-parent fsync failures were swallowed"
                )
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if (
            failed_stage_parent_fsyncs < 2
            or not durability_stage_root.is_dir()
        ):
            raise AssertionError(
                "postpublication stage durability fault did not preserve the exact stage"
            )
        repaired_stage_parent_fsyncs = 0

        def count_repaired_stage_parent_fsync(path: Path) -> None:
            nonlocal repaired_stage_parent_fsyncs
            if Path(path) == durability_stage_parent:
                repaired_stage_parent_fsyncs += 1
            original_fsync_directory(path)

        globals()["fsync_directory"] = count_repaired_stage_parent_fsync
        try:
            publish_or_verify_aggregation_stage(
                durability_aggregation,
                "01-report-products",
                atomic_files,
                static_lock_sha256="a" * 64,
                coordinator_actor_id="synthetic-runtime-coordinator-0001",
                prerequisite_stage_sha256=None,
                attempt_envelopes={},
            )
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if repaired_stage_parent_fsyncs < 1:
            raise AssertionError(
                "pre-existing aggregation stage did not repair parent durability"
            )
        prefix_hole_root = temporary_root / "aggregation-prefix-hole"
        (prefix_hole_root / "derived" / "02-scorer-products").mkdir(parents=True)
        try:
            validate_aggregation_directory_inventory(
                prefix_hole_root, require_final=False
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("aggregation stage-prefix hole was accepted")
        terminal_attempts: dict[str, dict[str, Any]] = {}
        terminal_slot_rows: list[dict[str, Any]] = []
        for index in range(1, 121):
            assignment = f"r{index:03d}"
            digest = sha256(assignment.encode("ascii"))
            failing = assignment == "r001"
            pointer_row = {
                "envelope_sha256": digest,
                "format_valid": not failing,
                "semantic_valid": not failing,
            }
            terminal_attempts[assignment] = {
                "status": "SEALED",
                "launch": {"role": "report"},
                "pointer": pointer_row,
                "primary_bytes": None if failing else b"report\n",
            }
            terminal_slot_rows.append(
                {
                    "slot_id": assignment,
                    "status": "SEALED",
                    "role": "report",
                    "envelope_sha256": digest,
                    "primary_output_present": not failing,
                    "format_valid": not failing,
                    "semantic_valid": not failing,
                }
            )
        terminal_document = build_aggregation_terminal_failure(
            blocked_stage_id="01-report-products",
            static_lock_sha256="b" * 64,
            coordinator_actor_id="synthetic-runtime-coordinator-0001",
            prerequisite_stage_sha256=None,
            attempts=terminal_attempts,
            cumulative_assignments=set(terminal_attempts),
            failure_assignments={"r001"},
        )
        validate_aggregation_attempt_bindings(
            (), [], terminal_slot_rows, terminal_document
        )
        terminal_durability_root = temporary_root / "terminal-durability"
        terminal_durability_path = (
            terminal_durability_root / AGGREGATION_TERMINAL_FAILURE
        )
        original_fsync_directory = globals()["fsync_directory"]
        failed_terminal_parent_fsyncs = 0

        def fail_published_terminal_parent_fsync(path: Path) -> None:
            nonlocal failed_terminal_parent_fsyncs
            if (
                Path(path) == terminal_durability_root
                and path_entry_exists(terminal_durability_path)
            ):
                failed_terminal_parent_fsyncs += 1
                raise OSError(
                    "synthetic postpublication terminal parent fsync failure"
                )
            original_fsync_directory(path)

        globals()["fsync_directory"] = fail_published_terminal_parent_fsync
        try:
            try:
                publish_or_verify_aggregation_terminal_failure(
                    terminal_durability_root, terminal_document
                )
            except OSError:
                pass
            else:
                raise AssertionError(
                    "exhausted terminal-parent fsync failures were swallowed"
                )
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if (
            failed_terminal_parent_fsyncs < 2
            or not terminal_durability_path.is_file()
        ):
            raise AssertionError(
                "postpublication terminal durability fault lost its exact record"
            )
        repaired_terminal_parent_fsyncs = 0

        def count_repaired_terminal_parent_fsync(path: Path) -> None:
            nonlocal repaired_terminal_parent_fsyncs
            if Path(path) == terminal_durability_root:
                repaired_terminal_parent_fsyncs += 1
            original_fsync_directory(path)

        globals()["fsync_directory"] = count_repaired_terminal_parent_fsync
        try:
            publish_or_verify_aggregation_terminal_failure(
                terminal_durability_root, terminal_document
            )
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if repaired_terminal_parent_fsyncs < 1:
            raise AssertionError(
                "pre-existing terminal failure did not repair parent durability"
            )
        format_only_report = {
            "r001": {
                "status": "SEALED",
                "launch": {"role": "report"},
                "pointer": {
                    "envelope_sha256": "c" * 64,
                    "format_valid": False,
                    "semantic_valid": True,
                },
                "primary_bytes": b"usable UTF-8 report\n",
            }
        }
        if aggregation_phase_failure_assignments(
            format_only_report, {"r001"}, report_phase=True
        ):
            raise AssertionError("usable format-only report incorrectly terminalized")
        if aggregation_phase_failure_assignments(
            format_only_report, {"r001"}, report_phase=False
        ) != {"r001"}:
            raise AssertionError("invalid evaluator format did not terminalize")
        forged_terminal = copy.deepcopy(terminal_document)
        forged_terminal["failures"] = []
        try:
            validate_aggregation_terminal_failure(forged_terminal)
        except ProtocolError:
            pass
        else:
            raise AssertionError("empty aggregation terminal-failure set was accepted")
        try:
            validate_aggregation_attempt_bindings(
                (),
                [],
                [
                    *terminal_slot_rows,
                    {
                        "slot_id": "E-s1",
                        "status": "STARTED",
                        "format_valid": False,
                        "semantic_valid": False,
                    },
                ],
                terminal_document,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError("terminal aggregation accepted a premature started slot")

        clean_report_rows = [
            {
                **row,
                "primary_output_present": True,
                "format_valid": True,
                "semantic_valid": True,
            }
            for row in terminal_slot_rows
        ]
        scorer_assignments = {
            f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS
        }
        consistency_assignments = {
            f"{mode}-{reviewer}"
            for mode in MODES
            for reviewer in CONSISTENCY_REVIEWERS
        }
        report_assignments = set(terminal_attempts)

        def synthetic_slot_row(
            assignment_id: str, role: str, *, valid: bool = True
        ) -> dict[str, Any]:
            return {
                "slot_id": assignment_id,
                "status": "SEALED",
                "role": role,
                "envelope_sha256": sha256(assignment_id.encode("ascii")),
                "primary_output_present": valid,
                "format_valid": valid,
                "semantic_valid": valid,
            }

        final_join_rows = [
            *clean_report_rows,
            *[
                synthetic_slot_row(
                    assignment,
                    "scorer",
                    valid=assignment != "E-s1",
                )
                for assignment in sorted(scorer_assignments)
            ],
            *[
                synthetic_slot_row(assignment, "consistency")
                for assignment in sorted(consistency_assignments)
            ],
            *[
                synthetic_slot_row(assignment, "materiality-reviewer")
                for assignment in MATERIALITY_REVIEWERS
            ],
        ]
        final_join_digest_by_slot = {
            row["slot_id"]: row["envelope_sha256"] for row in final_join_rows
        }
        cumulative_by_stage = {
            "01-report-products": report_assignments,
            "02-scorer-products": report_assignments | scorer_assignments,
            "03-consistency-products": report_assignments
            | scorer_assignments
            | consistency_assignments,
            "04-score-products": report_assignments
            | scorer_assignments
            | consistency_assignments,
            "05-materiality-products": report_assignments
            | scorer_assignments
            | consistency_assignments
            | set(MATERIALITY_REVIEWERS),
            "final": report_assignments
            | scorer_assignments
            | consistency_assignments
            | set(MATERIALITY_REVIEWERS),
        }
        final_join_manifests: list[dict[str, Any]] = []
        final_join_prerequisite: str | None = None
        for stage_id in AGGREGATION_STAGE_ORDER:
            manifest = build_aggregation_stage_manifest(
                stage_id,
                {},
                static_lock_sha256="d" * 64,
                coordinator_actor_id="synthetic-runtime-coordinator-0001",
                prerequisite_stage_sha256=final_join_prerequisite,
                attempt_envelopes={
                    assignment: final_join_digest_by_slot[assignment]
                    for assignment in cumulative_by_stage[stage_id]
                },
            )
            final_join_manifests.append(manifest)
            final_join_prerequisite = aggregation_stage_digest(manifest)
        try:
            validate_aggregation_attempt_bindings(
                AGGREGATION_STAGE_ORDER,
                final_join_manifests,
                final_join_rows,
                None,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError(
                "final aggregation accepted an invalid committed scorer phase"
            )

        late_terminal_attempts = copy.deepcopy(terminal_attempts)
        late_terminal_rows = list(terminal_slot_rows)
        for assignment in sorted(scorer_assignments):
            failing = assignment == "E-s1"
            digest = sha256(assignment.encode("ascii"))
            late_terminal_attempts[assignment] = {
                "status": "SEALED",
                "launch": {"role": "scorer"},
                "pointer": {
                    "envelope_sha256": digest,
                    "format_valid": not failing,
                    "semantic_valid": not failing,
                },
                "primary_bytes": None if failing else b"{}\n",
            }
            late_terminal_rows.append(
                synthetic_slot_row(assignment, "scorer", valid=not failing)
            )
        late_stage_one = build_aggregation_stage_manifest(
            "01-report-products",
            {},
            static_lock_sha256="e" * 64,
            coordinator_actor_id="synthetic-runtime-coordinator-0001",
            prerequisite_stage_sha256=None,
            attempt_envelopes={
                row["slot_id"]: row["envelope_sha256"]
                for row in terminal_slot_rows
            },
        )
        late_terminal = build_aggregation_terminal_failure(
            blocked_stage_id="02-scorer-products",
            static_lock_sha256="e" * 64,
            coordinator_actor_id="synthetic-runtime-coordinator-0001",
            prerequisite_stage_sha256=aggregation_stage_digest(late_stage_one),
            attempts=late_terminal_attempts,
            cumulative_assignments=set(late_terminal_attempts),
            failure_assignments={"E-s1"},
        )
        try:
            validate_aggregation_attempt_bindings(
                ("01-report-products",),
                [late_stage_one],
                late_terminal_rows,
                late_terminal,
            )
        except ProtocolError:
            pass
        else:
            raise AssertionError(
                "later terminal failure masked an invalid committed report phase"
            )
        receipt_bundle = temporary_root / "bound-receipt-bundle"
        aggregation_root = receipt_bundle / "runtime" / "state" / "aggregation"
        coordinator_actor = "synthetic-runtime-coordinator-0001"
        receipts = build_bound_aggregate_receipts(aggregate, coordinator_actor)
        final_files = {
            "aggregate-context.json": canonical_json_bytes(aggregate),
            **{
                f"integration-receipts/{hook_id}.json": canonical_json_bytes(receipt)
                for hook_id, receipt in receipts.items()
            },
        }
        publish_or_verify_aggregation_stage(
            aggregation_root,
            "final",
            final_files,
            static_lock_sha256=aggregate["static_lock_sha256"],
            coordinator_actor_id=coordinator_actor,
            prerequisite_stage_sha256="d" * 64,
            attempt_envelopes={},
        )
        receipt_root = aggregation_root / "final" / "integration-receipts"
        bind_path = receipt_root / "H-BIND-CONTEXT-INPUT-DIGESTS.json"
        validate_bound_aggregate_receipts(receipt_bundle, aggregate)
        os.chmod(receipt_root, 0o700)
        os.chmod(bind_path, 0o600)
        bad_bind = copy.deepcopy(receipts["H-BIND-CONTEXT-INPUT-DIGESTS"])
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
        durable_mkdir(state)
        exclusive_residue = state / (".exclusive-stage-orphan-" + "0" * 24)
        exclusive_residue.write_bytes(b"complete but unpublished")
        os.chmod(exclusive_residue, 0o400)
        with operation_lock(state):
            recover_exclusive_write_residues(state)
        if exclusive_residue.exists() or exclusive_residue.is_symlink():
            raise AssertionError("exclusive-write crash residue was not recoverable")
        spec_path = temporary_root / "spec.json"
        spec = {
            "schema_version": 1,
            "status": "READY",
            "files": [{"path": "report.md", "required": True, "max_bytes": 32768, "utf8": True}],
            "final_response": {
                "required": True,
                "max_bytes": 1024,
                "utf8": True,
                "utf8_fullmatch_regex": "^report\\.md\\n?$",
            },
            "max_total_output_bytes": 32768,
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

        invalid_terminal_requests: tuple[
            tuple[str, bytes | None, Any, Any, Any], ...
        ] = (
            ("empty-disposition", b"report.md\n", "", 0, {}),
            ("typed-disposition", b"report.md\n", 7, 0, {}),
            ("boolean-exit", b"report.md\n", "returned", True, {}),
            ("typed-response", "report.md\n", "returned", 0, {}),
            (
                "surrogate-metadata",
                b"report.md\n",
                "returned",
                0,
                {"bad": "\ud800"},
            ),
        )
        for (
            invalid_name,
            invalid_response,
            invalid_disposition,
            invalid_exit_code,
            invalid_metadata,
        ) in invalid_terminal_requests:
            invalid_state = temporary_root / f"invalid-terminal-{invalid_name}-state"
            invalid_output = (
                temporary_root / f"invalid-terminal-{invalid_name}-workspace" / "output"
            )
            invalid_lease = synthetic_lease(
                "slot-one",
                f"invalid-terminal-{invalid_name}-agent",
                invalid_output,
                lease_state=invalid_state,
            )
            (invalid_output / "report.md").write_text(
                "terminal request preflight\n", encoding="utf-8"
            )
            try:
                synthetic_seal(
                    invalid_state,
                    "slot-one",
                    invalid_lease["lease_token"],
                    invalid_lease["agent_id"],
                    invalid_output,
                    invalid_response,
                    invalid_disposition,
                    invalid_exit_code,
                    invalid_metadata,
                )
            except ProtocolError:
                pass
            else:
                raise AssertionError(
                    f"invalid terminal request was accepted: {invalid_name}"
                )
            invalid_slot = invalid_state / "slots" / "slot-one"
            invalid_objects = invalid_state / "objects" / "sha256"
            if any(
                path_entry_exists(invalid_slot / name)
                for name in (
                    "terminal-claim.json",
                    "canonical.json",
                    "seal-failure.json",
                )
            ) or (
                path_entry_exists(invalid_objects)
                and any(
                    path.name.startswith(".stage-")
                    for path in invalid_objects.iterdir()
                )
            ):
                raise AssertionError(
                    f"invalid terminal request mutated state: {invalid_name}"
                )
            invalid_verified = synthetic_verify(invalid_state)
            if (
                invalid_verified["state_valid"] is not True
                or invalid_verified["slots"][0]["status"] != "STARTED"
            ):
                raise AssertionError(
                    f"invalid terminal request poisoned its lease: {invalid_name}"
                )

        dangling_state = temporary_root / "dangling-ledger-state"
        dangling_output = temporary_root / "dangling-ledger-workspace" / "output"
        synthetic_lease(
            "slot-one",
            "dangling-ledger-agent",
            dangling_output,
            lease_state=dangling_state,
        )
        dangling_slot = dangling_state / "slots" / "slot-one"
        ready_path = dangling_slot / "lease-ready.json"
        ready_bytes = ready_path.read_bytes()
        for dangling_name in (
            "lease-failure.json",
            "terminal-claim.json",
            "canonical.json",
            "seal-failure.json",
        ):
            dangling_path = dangling_slot / dangling_name
            os.symlink("missing-ledger-target", dangling_path)
            try:
                synthetic_verify(dangling_state)
            except ProtocolError:
                pass
            else:
                raise AssertionError(
                    f"dangling {dangling_name} ledger was treated as absent"
                )
            dangling_path.unlink()
        ready_path.unlink()
        os.symlink("missing-ledger-target", ready_path)
        try:
            synthetic_verify(dangling_state)
        except ProtocolError:
            pass
        else:
            raise AssertionError("dangling lease-ready ledger was treated as absent")
        ready_path.unlink()
        exclusive_write(ready_path, ready_bytes)

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
            "evaluator_contract_index": globals()["evaluator_contract_index"],
            "load_authoritative_evaluator_material": globals()[
                "load_authoritative_evaluator_material"
            ],
            "materialize_evaluator_input_tree": globals()["materialize_evaluator_input_tree"],
        }
        active_production_launch = [production_launch]
        active_production_launch_path = [production_launch_path]
        forbid_production_materialization = [False]
        globals()["load_verified_static_bundle"] = (
            lambda static_root, external_commitment_path=None: (
                Path(static_root).resolve(),
                {"status": "STATIC-LOCKED"},
                production_reviewer_ids,
            )
        )
        globals()["load_ready_generated_documents"] = lambda _root: {}
        globals()["evaluator_contract_index"] = lambda _documents: {
            active_production_launch[0]["assignment_id"]: {}
        }
        globals()["load_authoritative_evaluator_material"] = (
            lambda _root, _assignment, *, capability=None, ready_documents=None: (
                input_packet_path,
                active_production_launch_path[0],
                production_spec_path,
                strict_json_loads(input_packet_path.read_bytes(), "synthetic packet"),
                active_production_launch[0],
            )
        )
        def mock_production_materialization(*args: Any) -> None:
            if forbid_production_materialization[0]:
                raise AssertionError(
                    "poisoned peer was detected only after input materialization"
                )
            input_root = Path(args[0])
            input_root.mkdir(parents=True, exist_ok=True)
            os.chmod(input_root, 0o500)

        globals()["materialize_evaluator_input_tree"] = mock_production_materialization
        try:
            production_reserved_ids = production_reviewer_ids | {
                "aggregation-coordinator-0001"
            }
            try:
                acquire_lease(
                    production_mock_root / "runtime" / "state",
                    production_launch_path,
                    "runtime-agent-9999",
                    production_spec_path,
                    production_output,
                    input_packet_path,
                    static_root=production_mock_root,
                    external_commitment_path=commitment_path,
                )
            except ProtocolError as error:
                if "assignment-only production wrapper" not in str(error):
                    raise AssertionError(
                        "generic production acquisition failed for the wrong reason"
                    ) from error
            else:
                raise AssertionError("generic production acquisition remained reachable")
            production_lease = acquire_lease(
                production_mock_root / "runtime" / "state",
                production_launch_path,
                "runtime-agent-9999",
                production_spec_path,
                production_output,
                input_packet_path,
                production_context=(
                    production_mock_root,
                    production_reserved_ids,
                ),
                production_capability=_PRODUCTION_LEASE_CAPABILITY,
            )
            if production_lease["agent_id"] != "runtime-agent-9999":
                raise AssertionError("production acquisition changed its actor identity")

            def make_production_launch(
                slot_id: str, assignment_id: str
            ) -> tuple[dict[str, Any], Path, Path]:
                workspace = temporary_root / f"{slot_id}-workspace"
                input_root = workspace / "input"
                output_root = workspace / "output"
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
            active_production_launch_path[0] = second_launch_path
            second_lease = acquire_lease(
                production_mock_root / "runtime" / "state",
                second_launch_path,
                "runtime-agent-9998",
                production_spec_path,
                second_output,
                input_packet_path,
                production_context=(
                    production_mock_root,
                    production_reserved_ids,
                ),
                production_capability=_PRODUCTION_LEASE_CAPABILITY,
            )
            if second_lease["agent_id"] != "runtime-agent-9998":
                raise AssertionError("second production acquisition changed its actor identity")
            try:
                active_production_launch[0] = production_launch
                active_production_launch_path[0] = production_launch_path
                acquire_lease(
                    production_mock_root / "runtime" / "state",
                    production_launch_path,
                    "reviewer-actor-0001",
                    production_spec_path,
                    production_output,
                    input_packet_path,
                    production_context=(
                        production_mock_root,
                        production_reserved_ids,
                    ),
                    production_capability=_PRODUCTION_LEASE_CAPABILITY,
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
                active_production_launch_path[0] = target_launch_path
                forbid_production_materialization[0] = True
                try:
                    acquire_lease(
                        poisoned_acquire_root / "runtime/state",
                        target_launch_path,
                        f"runtime-agent-88{poison_index:02d}",
                        poisoned_acquire_root / "spec.json",
                        target_output,
                        input_packet_path,
                        production_context=(
                            poisoned_acquire_root,
                            production_reserved_ids,
                        ),
                        production_capability=_PRODUCTION_LEASE_CAPABILITY,
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
                        production_context=(
                            poisoned_seal_root,
                            production_reserved_ids,
                        ),
                        production_capability=_PRODUCTION_LEASE_CAPABILITY,
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

        for fault_point in (
            "envelope-capture",
            "object-publish",
            "canonical-cas",
            "canonical-pointer",
        ):
            fault_state = temporary_root / f"seal-fault-state-{fault_point}"
            fault_output = (
                temporary_root / f"seal-fault-workspace-{fault_point}" / "output"
            )
            fault_lease = synthetic_lease(
                "slot-one",
                f"seal-fault-agent-{fault_point}",
                fault_output,
                lease_state=fault_state,
            )
            (fault_output / "report.md").write_text(
                "fault recovery report\n", encoding="utf-8"
            )
            seal_arguments = (
                fault_state,
                "slot-one",
                fault_lease["lease_token"],
                f"seal-fault-agent-{fault_point}",
                fault_output,
                b"report.md\n",
                "returned",
                0,
                {"fault_point": fault_point},
            )
            try:
                synthetic_seal(*seal_arguments, fault_after=fault_point)
            except InjectedFault:
                pass
            else:
                raise AssertionError(
                    f"seal fault injection did not fire: {fault_point}"
                )
            recovered_pointer = synthetic_seal(*seal_arguments)
            canonical_fault_path = (
                fault_state / "slots" / "slot-one" / "canonical.json"
            )
            canonical_before = canonical_fault_path.read_bytes()
            try:
                synthetic_seal(
                    *seal_arguments[:-1],
                    {"fault_point": fault_point, "changed": True},
                )
            except TerminalAlreadyClaimed:
                pass
            else:
                raise AssertionError(
                    f"changed seal recovery arguments were accepted: {fault_point}"
                )
            if canonical_fault_path.read_bytes() != canonical_before:
                raise AssertionError("failed seal retry mutated the canonical pointer")
            recovered_state = synthetic_verify(fault_state)
            recovered_row = next(
                row
                for row in recovered_state["slots"]
                if row["slot_id"] == "slot-one"
            )
            if (
                recovered_row["status"] != "SEALED"
                or recovered_row["envelope_sha256"]
                != recovered_pointer["envelope_sha256"]
                or recovered_state["staging_entries"]
            ):
                raise AssertionError(
                    f"seal recovery state is incomplete: {fault_point}"
                )

        object_durability_state = temporary_root / "object-durability-state"
        object_durability_output = (
            temporary_root / "object-durability-workspace" / "output"
        )
        object_durability_lease = synthetic_lease(
            "slot-one",
            "object-durability-agent",
            object_durability_output,
            lease_state=object_durability_state,
        )
        (object_durability_output / "report.md").write_text(
            "object durability report\n", encoding="utf-8"
        )
        object_durability_arguments = (
            object_durability_state,
            "slot-one",
            object_durability_lease["lease_token"],
            "object-durability-agent",
            object_durability_output,
            b"report.md\n",
            "returned",
            0,
            {"durability": "object-parent"},
        )
        object_parent = object_durability_state / "objects" / "sha256"
        original_fsync_directory = globals()["fsync_directory"]
        failed_object_parent_fsyncs = 0

        def fail_published_object_parent_fsync(path: Path) -> None:
            nonlocal failed_object_parent_fsyncs
            published_object_exists = object_parent.is_dir() and any(
                child.is_dir() and HEX64.fullmatch(child.name) is not None
                for child in object_parent.iterdir()
            )
            if Path(path) == object_parent and published_object_exists:
                failed_object_parent_fsyncs += 1
                raise OSError(
                    "synthetic postpublication object-parent fsync failure"
                )
            original_fsync_directory(path)

        globals()["fsync_directory"] = fail_published_object_parent_fsync
        try:
            try:
                synthetic_seal(*object_durability_arguments)
            except OSError:
                pass
            else:
                raise AssertionError(
                    "exhausted object-parent fsync failures were swallowed"
                )
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        object_durability_slot = (
            object_durability_state / "slots" / "slot-one"
        )
        if (
            failed_object_parent_fsyncs < 2
            or not path_entry_exists(
                object_durability_slot / "terminal-claim.json"
            )
            or path_entry_exists(object_durability_slot / "canonical.json")
            or path_entry_exists(object_durability_slot / "seal-failure.json")
        ):
            raise AssertionError(
                "postpublication object durability fault poisoned recovery state"
            )
        repaired_object_parent_fsyncs = 0

        def count_repaired_object_parent_fsync(path: Path) -> None:
            nonlocal repaired_object_parent_fsyncs
            if Path(path) == object_parent:
                repaired_object_parent_fsyncs += 1
            original_fsync_directory(path)

        globals()["fsync_directory"] = count_repaired_object_parent_fsync
        try:
            synthetic_seal(*object_durability_arguments)
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if repaired_object_parent_fsyncs < 1:
            raise AssertionError(
                "pre-existing envelope object did not repair parent durability"
            )

        original_immutable_writer = globals()["_write_or_validate_immutable"]
        for claim_kind in ("agent", "attempt-root"):
            claim_exception_state = (
                temporary_root / f"{claim_kind}-claim-postpublish-state"
            )
            claim_exception_output = (
                temporary_root
                / f"{claim_kind}-claim-postpublish-workspace"
                / "output"
            )
            claim_exception_fired = [False]

            def raise_after_claim_publish(
                path: Path,
                value: dict[str, Any],
                *,
                expected_kind: str = claim_kind,
            ) -> None:
                original_immutable_writer(path, value)
                is_expected = (
                    expected_kind == "agent"
                    and path.name == "claim.json"
                    and path.parent.parent.name == "agents"
                ) or (
                    expected_kind == "attempt-root"
                    and path.parent.name == "attempt-roots"
                )
                if is_expected and not claim_exception_fired[0]:
                    claim_exception_fired[0] = True
                    raise OSError(
                        f"synthetic post-{expected_kind}-claim publication failure"
                    )

            globals()["_write_or_validate_immutable"] = raise_after_claim_publish
            try:
                try:
                    synthetic_lease(
                        "slot-one",
                        f"{claim_kind}-claim-postpublish-agent",
                        claim_exception_output,
                        lease_state=claim_exception_state,
                    )
                except OSError:
                    pass
                else:
                    raise AssertionError(
                        f"post-{claim_kind}-claim exception was swallowed before readiness"
                    )
            finally:
                globals()["_write_or_validate_immutable"] = original_immutable_writer
            persisted_claim_lease = validate_lease(
                read_json(
                    claim_exception_state
                    / "slots"
                    / "slot-one"
                    / "lease.json"
                )
            )
            recovered_claim_lease = synthetic_lease(
                "slot-one",
                f"{claim_kind}-claim-postpublish-agent",
                claim_exception_output,
                lease_state=claim_exception_state,
            )
            if (
                not claim_exception_fired[0]
                or recovered_claim_lease != persisted_claim_lease
                or path_entry_exists(
                    claim_exception_state
                    / "slots"
                    / "slot-one"
                    / "lease-failure.json"
                )
            ):
                raise AssertionError(
                    f"post-{claim_kind}-claim exception was not idempotently recoverable"
                )

        ready_exception_state = temporary_root / "ready-postpublish-state"
        ready_exception_output = (
            temporary_root / "ready-postpublish-workspace" / "output"
        )
        ready_exception_fired = [False]

        def raise_after_ready_publish(path: Path, value: dict[str, Any]) -> None:
            original_immutable_writer(path, value)
            if path.name == "lease-ready.json" and not ready_exception_fired[0]:
                ready_exception_fired[0] = True
                raise OSError("synthetic post-ready publication failure")

        globals()["_write_or_validate_immutable"] = raise_after_ready_publish
        try:
            ready_exception_lease = synthetic_lease(
                "slot-one",
                "ready-postpublish-agent",
                ready_exception_output,
                lease_state=ready_exception_state,
            )
        finally:
            globals()["_write_or_validate_immutable"] = original_immutable_writer
        ready_exception_slot = ready_exception_state / "slots" / "slot-one"
        if (
            not ready_exception_fired[0]
            or path_entry_exists(ready_exception_slot / "lease-failure.json")
            or synthetic_verify(ready_exception_state)["slots"][0]["status"]
            != "STARTED"
        ):
            raise AssertionError(
                "post-publication ready exception created contradictory lease state"
            )

        canonical_exception_state = temporary_root / "canonical-postpublish-state"
        canonical_exception_output = (
            temporary_root / "canonical-postpublish-workspace" / "output"
        )
        canonical_exception_lease = synthetic_lease(
            "slot-one",
            "canonical-postpublish-agent",
            canonical_exception_output,
            lease_state=canonical_exception_state,
        )
        (canonical_exception_output / "report.md").write_text(
            "canonical postpublication recovery\n", encoding="utf-8"
        )
        canonical_exception_fired = [False]

        def raise_after_canonical_publish(
            path: Path, value: dict[str, Any]
        ) -> None:
            original_immutable_writer(path, value)
            if path.name == "canonical.json" and not canonical_exception_fired[0]:
                canonical_exception_fired[0] = True
                raise OSError("synthetic post-canonical publication failure")

        globals()["_write_or_validate_immutable"] = raise_after_canonical_publish
        try:
            canonical_exception_pointer = synthetic_seal(
                canonical_exception_state,
                "slot-one",
                canonical_exception_lease["lease_token"],
                canonical_exception_lease["agent_id"],
                canonical_exception_output,
                b"report.md\n",
                "returned",
                0,
                {"synthetic": "postpublication"},
            )
        finally:
            globals()["_write_or_validate_immutable"] = original_immutable_writer
        canonical_exception_verified = synthetic_verify(canonical_exception_state)
        if (
            not canonical_exception_fired[0]
            or path_entry_exists(
                canonical_exception_state
                / "slots"
                / "slot-one"
                / "seal-failure.json"
            )
            or canonical_exception_verified["slots"][0]["status"] != "SEALED"
            or canonical_exception_verified["slots"][0]["envelope_sha256"]
            != canonical_exception_pointer["envelope_sha256"]
        ):
            raise AssertionError(
                "post-publication canonical exception created contradictory seal state"
            )

        claim_exception_state = temporary_root / "terminal-claim-postpublish-state"
        claim_exception_output = (
            temporary_root / "terminal-claim-postpublish-workspace" / "output"
        )
        claim_exception_lease = synthetic_lease(
            "slot-one",
            "terminal-claim-postpublish-agent",
            claim_exception_output,
            lease_state=claim_exception_state,
        )
        (claim_exception_output / "report.md").write_text(
            "terminal claim postpublication recovery\n", encoding="utf-8"
        )
        terminal_claim_exception_fired = [False]

        def raise_after_terminal_claim_publish(
            path: Path, value: dict[str, Any]
        ) -> None:
            original_immutable_writer(path, value)
            if (
                path.name == "terminal-claim.json"
                and not terminal_claim_exception_fired[0]
            ):
                terminal_claim_exception_fired[0] = True
                raise OSError("synthetic post-terminal-claim publication failure")

        globals()["_write_or_validate_immutable"] = raise_after_terminal_claim_publish
        terminal_claim_arguments = (
            claim_exception_state,
            "slot-one",
            claim_exception_lease["lease_token"],
            claim_exception_lease["agent_id"],
            claim_exception_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": "terminal-claim-postpublication"},
        )
        try:
            try:
                synthetic_seal(*terminal_claim_arguments)
            except OSError:
                pass
            else:
                raise AssertionError(
                    "post-terminal-claim exception was swallowed before canonical publication"
                )
        finally:
            globals()["_write_or_validate_immutable"] = original_immutable_writer
        claim_exception_slot = claim_exception_state / "slots" / "slot-one"
        if (
            not terminal_claim_exception_fired[0]
            or not path_entry_exists(claim_exception_slot / "terminal-claim.json")
            or path_entry_exists(claim_exception_slot / "seal-failure.json")
        ):
            raise AssertionError(
                "post-terminal-claim exception did not preserve retryable state"
            )
        terminal_claim_pointer = synthetic_seal(*terminal_claim_arguments)
        terminal_claim_verified = synthetic_verify(claim_exception_state)
        if (
            terminal_claim_verified["slots"][0]["status"] != "SEALED"
            or terminal_claim_verified["slots"][0]["envelope_sha256"]
            != terminal_claim_pointer["envelope_sha256"]
            or path_entry_exists(claim_exception_slot / "seal-failure.json")
        ):
            raise AssertionError(
                "post-terminal-claim exception was not idempotently recoverable"
            )

        failure_durability_state = temporary_root / "seal-failure-durability-state"
        failure_durability_output = (
            temporary_root / "seal-failure-durability-workspace" / "output"
        )
        failure_durability_lease = synthetic_lease(
            "slot-one",
            "seal-failure-durability-agent",
            failure_durability_output,
            lease_state=failure_durability_state,
        )
        (failure_durability_output / "report.md").write_text(
            "seal failure durability\n", encoding="utf-8"
        )
        failure_durability_slot = (
            failure_durability_state / "slots" / "slot-one"
        )
        failure_durability_path = failure_durability_slot / "seal-failure.json"
        failure_durability_arguments = (
            failure_durability_state,
            "slot-one",
            failure_durability_lease["lease_token"],
            "seal-failure-durability-agent",
            failure_durability_output,
            b"report.md\n",
            "returned",
            0,
            {"durability": "seal-failure-parent"},
        )
        destroyed_failure_stage = False

        def destroy_stage_after_terminal_claim(
            path: Path, value: dict[str, Any]
        ) -> None:
            nonlocal destroyed_failure_stage
            original_immutable_writer(path, value)
            if path.name == "terminal-claim.json" and not destroyed_failure_stage:
                stages = sorted(
                    (
                        failure_durability_state / "objects" / "sha256"
                    ).glob(f".stage-{failure_durability_lease['attempt_id']}-*")
                )
                if len(stages) != 1:
                    raise AssertionError(
                        "seal-failure durability fixture lacks its private stage"
                    )
                _discard_private_aggregation_stage(stages[0])
                destroyed_failure_stage = True
                raise OSError("synthetic nonrecoverable post-claim failure")

        original_fsync_directory = globals()["fsync_directory"]
        failed_seal_failure_parent_fsyncs = 0

        def fail_seal_failure_parent_fsync(path: Path) -> None:
            nonlocal failed_seal_failure_parent_fsyncs
            if (
                Path(path) == failure_durability_slot
                and path_entry_exists(failure_durability_path)
            ):
                failed_seal_failure_parent_fsyncs += 1
                raise OSError(
                    "synthetic postpublication seal-failure parent fsync failure"
                )
            original_fsync_directory(path)

        globals()["_write_or_validate_immutable"] = (
            destroy_stage_after_terminal_claim
        )
        globals()["fsync_directory"] = fail_seal_failure_parent_fsync
        try:
            try:
                synthetic_seal(*failure_durability_arguments)
            except OSError:
                pass
            else:
                raise AssertionError(
                    "nonrecoverable post-claim seal failure was swallowed"
                )
        finally:
            globals()["_write_or_validate_immutable"] = original_immutable_writer
            globals()["fsync_directory"] = original_fsync_directory
        if (
            not destroyed_failure_stage
            or failed_seal_failure_parent_fsyncs < 3
            or not path_entry_exists(failure_durability_path)
        ):
            raise AssertionError(
                "seal-failure durability fixture did not publish its failed outcome"
            )
        repaired_seal_failure_parent_fsyncs = 0

        def count_repaired_seal_failure_parent_fsync(path: Path) -> None:
            nonlocal repaired_seal_failure_parent_fsyncs
            if Path(path) == failure_durability_slot:
                repaired_seal_failure_parent_fsyncs += 1
            original_fsync_directory(path)

        globals()["fsync_directory"] = count_repaired_seal_failure_parent_fsync
        try:
            try:
                synthetic_seal(*failure_durability_arguments)
            except TerminalAlreadyClaimed:
                pass
            else:
                raise AssertionError(
                    "committed seal failure did not remain terminal on retry"
                )
        finally:
            globals()["fsync_directory"] = original_fsync_directory
        if repaired_seal_failure_parent_fsyncs < 1:
            raise AssertionError(
                "pre-existing seal failure did not repair parent durability"
            )
        failure_durability_verified = synthetic_verify(failure_durability_state)
        if failure_durability_verified["slots"][0]["status"] != "SEAL_FAILED":
            raise AssertionError("repaired seal-failure state did not verify")

        invalid_path_state = temporary_root / "invalid-output-path-state"
        invalid_path_output = (
            temporary_root / "invalid-output-path-workspace" / "output"
        )
        invalid_path_lease = synthetic_lease(
            "slot-one",
            "invalid-output-path-agent",
            invalid_path_output,
            lease_state=invalid_path_state,
        )
        (invalid_path_output / "report.md").write_text(
            "synthetic report\n", encoding="utf-8"
        )
        (invalid_path_output / "bad\\name").write_bytes(b"backslash path\n")
        unreadable_file = invalid_path_output / "unreadable-file.txt"
        unreadable_file.write_bytes(b"owner-read restored during capture\n")
        os.chmod(unreadable_file, 0o000)
        unreadable_directory = invalid_path_output / "unreadable-directory"
        unreadable_directory.mkdir()
        unreadable_child = unreadable_directory / "child.txt"
        unreadable_child.write_bytes(b"nested owner-read restored during capture\n")
        os.chmod(unreadable_child, 0o000)
        os.chmod(unreadable_directory, 0o000)
        invalid_output_fd = os.open(
            invalid_path_output,
            os.O_RDONLY | getattr(os, "O_DIRECTORY", 0),
        )
        try:
            invalid_name_fd = os.open(
                b"bad-\xff",
                os.O_WRONLY | os.O_CREAT | os.O_EXCL,
                0o600,
                dir_fd=invalid_output_fd,
            )
            try:
                os.write(invalid_name_fd, b"non-utf8 path\n")
            finally:
                os.close(invalid_name_fd)
        finally:
            os.close(invalid_output_fd)
        os.chmod(invalid_path_output, 0o000)
        invalid_path_pointer = synthetic_seal(
            invalid_path_state,
            "slot-one",
            invalid_path_lease["lease_token"],
            "invalid-output-path-agent",
            invalid_path_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        if stat.S_IMODE(invalid_path_output.lstat().st_mode) != 0:
            raise AssertionError("output capture did not restore output-root mode")
        os.chmod(invalid_path_output, 0o700)
        if (
            stat.S_IMODE(unreadable_file.lstat().st_mode) != 0
            or stat.S_IMODE(unreadable_directory.lstat().st_mode) != 0
        ):
            raise AssertionError("output capture did not restore agent-selected modes")
        os.chmod(unreadable_directory, 0o700)
        if stat.S_IMODE(unreadable_child.lstat().st_mode) != 0:
            raise AssertionError("output capture did not restore nested file mode")
        os.chmod(unreadable_file, 0o600)
        os.chmod(unreadable_child, 0o600)
        if invalid_path_pointer["format_valid"] is not False:
            raise AssertionError("nonportable output paths were not format-invalid")
        invalid_path_envelope = read_json(
            invalid_path_state
            / "objects"
            / "sha256"
            / invalid_path_pointer["envelope_sha256"]
            / "envelope.json"
        )
        encoded_path_records = [
            row
            for row in invalid_path_envelope["output_entries"]
            if row["path"].startswith(ENCODED_OUTPUT_PATH_PREFIX)
        ]
        if len(encoded_path_records) != 2 or not any(
            violation.startswith("invalid-path:")
            for violation in invalid_path_envelope["violations"]
        ):
            raise AssertionError("nonportable POSIX paths were not captured injectively")
        invalid_path_verified = synthetic_verify(invalid_path_state)
        if (
            invalid_path_verified["state_valid"] is not True
            or invalid_path_verified["slots"][0]["status"] != "SEALED"
            or (
                invalid_path_state / "slots" / "slot-one" / "seal-failure.json"
            ).exists()
        ):
            raise AssertionError("nonportable output path stranded terminal sealing")
        invalid_path_object = (
            invalid_path_state
            / "objects"
            / "sha256"
            / invalid_path_pointer["envelope_sha256"]
        )
        injected_empty_directory = invalid_path_object / "unbound-empty-directory"
        os.chmod(invalid_path_object, 0o700)
        injected_empty_directory.mkdir()
        os.chmod(injected_empty_directory, 0o500)
        os.chmod(invalid_path_object, 0o500)
        try:
            synthetic_verify(invalid_path_state)
        except ProtocolError:
            pass
        else:
            raise AssertionError("unbound empty canonical-object directory was accepted")
        os.chmod(invalid_path_object, 0o700)
        os.chmod(injected_empty_directory, 0o700)
        injected_empty_directory.rmdir()
        os.chmod(invalid_path_object, 0o500)
        if synthetic_verify(invalid_path_state)["state_valid"] is not True:
            raise AssertionError("canonical object did not recover after tamper removal")

        report_overcap_workspace = temporary_root / "report-overcap-workspace"
        report_overcap_output = report_overcap_workspace / "output"
        report_overcap_spec = {
            "schema_version": 1,
            "status": "READY",
            "files": [
                {
                    "path": "report.md",
                    "required": True,
                    "max_bytes": 64,
                    "utf8": True,
                }
            ],
            "final_response": {
                "required": True,
                "max_bytes": 1024,
                "utf8": True,
                "utf8_fullmatch_regex": "^report\\.md\\n?$",
            },
            "max_total_output_bytes": 64,
            "allowed_process_dispositions": ["returned"],
        }
        report_overcap_spec_path = temporary_root / "report-overcap-spec.json"
        report_overcap_spec_bytes = canonical_json_bytes(report_overcap_spec)
        report_overcap_spec_path.write_bytes(report_overcap_spec_bytes)
        report_overcap_packet_path = temporary_root / "report-overcap-plan.json"
        report_overcap_packet_path.write_bytes(inventory_plan_bytes)
        report_overcap_launch = {
            **report_launch,
            "workspace_root": str(report_overcap_workspace),
            "input_root": str(report_overcap_workspace / "input"),
            "output_root": str(report_overcap_output),
            "input_packet_sha256": sha256(inventory_plan_bytes),
            "envelope_spec_sha256": sha256(report_overcap_spec_bytes),
        }
        report_overcap_launch_path = temporary_root / "report-overcap-launch.json"
        report_overcap_launch_path.write_bytes(
            canonical_json_bytes(report_overcap_launch)
        )
        report_overcap_launch_bytes = canonical_json_bytes(report_overcap_launch)
        report_overcap_lease = validate_lease(
            {
                **inventory_lease,
                "agent_id": "report-overcap-agent",
                "launch_record_sha256": sha256(report_overcap_launch_bytes),
                "launch_record_bytes_base64": base64.b64encode(
                    report_overcap_launch_bytes
                ).decode("ascii"),
                "attempt_root": str(report_overcap_output),
                "attempt_root_claim_sha256": sha256(
                    str(report_overcap_output).encode("utf-8")
                ),
                "envelope_spec_sha256": sha256(report_overcap_spec_bytes),
                "envelope_spec_bytes_base64": base64.b64encode(
                    report_overcap_spec_bytes
                ).decode("ascii"),
                "input_packet_sha256": sha256(inventory_plan_bytes),
                "input_packet_bytes_base64": base64.b64encode(
                    inventory_plan_bytes
                ).decode("ascii"),
            }
        )
        report_overcap_output.mkdir(parents=True)
        report_overcap_output.joinpath("report.md").write_bytes(b"r" * 65)
        report_overcap_stage = temporary_root / "report-overcap-envelope"
        report_overcap_stage.mkdir()
        report_overcap_envelope = capture_envelope(
            report_overcap_stage,
            report_overcap_lease,
            report_overcap_spec,
            report_overcap_output,
            b"x" * 1025,
            "returned",
            0,
            {"synthetic": True},
        )
        report_overcap_record = report_overcap_envelope["output_entries"][0]
        if (
            report_overcap_envelope["format_valid"] is not False
            or report_overcap_envelope["semantic_valid"] is not True
            or report_overcap_record["captured"] is not True
            or report_overcap_record["size"] != 65
            or report_overcap_envelope["final_response"]["captured"] is not True
            or "total-output-oversize:65:64"
            not in report_overcap_envelope["violations"]
            or "oversize:final-response:1025:1024"
            not in report_overcap_envelope["violations"]
        ):
            raise AssertionError(
                "ordinary spec-overcap report/final response did not remain captured"
            )
        with report_overcap_output.joinpath("report.md").open("wb") as sparse:
            sparse.truncate(MAX_ENVELOPE_CAPTURE_BYTES)
        aggregate_hard_stage = temporary_root / "aggregate-hard-envelope"
        aggregate_hard_stage.mkdir()
        aggregate_hard_envelope = capture_envelope(
            aggregate_hard_stage,
            report_overcap_lease,
            report_overcap_spec,
            report_overcap_output,
            b"x",
            "returned",
            0,
            {"synthetic": True},
        )
        if (
            aggregate_hard_envelope["output_entries"][0]["captured"] is not True
            or aggregate_hard_envelope["final_response"]["captured"] is not False
            or aggregate_hard_envelope["semantic_errors"]
            != ["semantic:output-capture-hard-limit"]
            or "uncaptured-oversize:final-response:1"
            not in aggregate_hard_envelope["violations"]
            or path_entry_exists(
                aggregate_hard_stage / "payload" / "final-response.bin"
            )
        ):
            raise AssertionError(
                "aggregate output/final-response hard byte limit was not enforced"
            )
        report_overcap_output.joinpath("report.md").write_bytes(b"usable report\n")
        report_hard_extra = report_overcap_output / "unexpected-large.bin"
        with report_hard_extra.open("wb") as sparse:
            sparse.truncate(64 * 1024 * 1024)
        report_hard_extra_stage = temporary_root / "report-hard-extra-envelope"
        report_hard_extra_stage.mkdir()
        report_hard_extra_envelope = capture_envelope(
            report_hard_extra_stage,
            report_overcap_lease,
            report_overcap_spec,
            report_overcap_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        report_primary_record = next(
            row
            for row in report_hard_extra_envelope["output_entries"]
            if row["path"] == "report.md"
        )
        if (
            report_primary_record["captured"] is not True
            or report_hard_extra_envelope["semantic_errors"]
            != ["semantic:output-capture-hard-limit"]
            or report_hard_extra_envelope["semantic_valid"] is not False
        ):
            raise AssertionError(
                "hard overflow in an extra report file did not terminalize semantics"
            )

        hard_cap_state = temporary_root / "hard-cap-state"
        hard_cap_output = temporary_root / "hard-cap-workspace" / "output"
        hard_cap_lease = synthetic_lease(
            "slot-invalid",
            "hard-cap-agent",
            hard_cap_output,
            lease_state=hard_cap_state,
        )
        hard_cap_primary = hard_cap_output / "report.md"
        with hard_cap_primary.open("wb") as sparse:
            sparse.truncate(64 * 1024 * 1024)
        hard_cap_pointer = synthetic_seal(
            hard_cap_state,
            "slot-invalid",
            hard_cap_lease["lease_token"],
            "hard-cap-agent",
            hard_cap_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        hard_cap_envelope = read_json(
            hard_cap_state
            / "objects"
            / "sha256"
            / hard_cap_pointer["envelope_sha256"]
            / "envelope.json"
        )
        hard_cap_record = hard_cap_envelope["output_entries"][0]
        if (
            hard_cap_record["captured"] is not False
            or hard_cap_record["size"] != 64 * 1024 * 1024
            or hard_cap_record["sha256"] is not None
            or hard_cap_pointer["semantic_valid"] is not False
            or synthetic_verify(hard_cap_state)["state_valid"] is not True
            or (hard_cap_state / "slots" / "slot-invalid" / "seal-failure.json").exists()
        ):
            raise AssertionError("hard-cap output did not terminalize canonically")
        oversized_final_response = read_bounded_final_response(
            hard_cap_primary,
            MAX_ENVELOPE_CAPTURE_BYTES,
            "synthetic oversized final-response input",
        )
        if (
            type(oversized_final_response) is not OversizedFinalResponse
            or oversized_final_response.size != 64 * 1024 * 1024
            or len(oversized_final_response.prefix)
            != MAX_ENVELOPE_CAPTURE_BYTES + 1
        ):
            raise AssertionError("oversized CLI-style input was not prefix bounded")

        hard_final_state = temporary_root / "hard-final-state"
        hard_final_output = temporary_root / "hard-final-workspace" / "output"
        hard_final_lease = synthetic_lease(
            "slot-invalid",
            "hard-final-agent",
            hard_final_output,
            lease_state=hard_final_state,
        )
        (hard_final_output / "report.md").write_bytes(b"{}\n")
        hard_final_pointer = synthetic_seal(
            hard_final_state,
            "slot-invalid",
            hard_final_lease["lease_token"],
            "hard-final-agent",
            hard_final_output,
            oversized_final_response,
            "returned",
            0,
            {"synthetic": True},
        )
        hard_final_envelope = read_json(
            hard_final_state
            / "objects"
            / "sha256"
            / hard_final_pointer["envelope_sha256"]
            / "envelope.json"
        )
        if (
            hard_final_envelope["final_response"]["captured"] is not False
            or hard_final_envelope["final_response"]["size"]
            != 64 * 1024 * 1024
            or hard_final_envelope["final_response"]["sha256"] is not None
            or hard_final_envelope["final_response"]["prefix_sha256"]
            != sha256(oversized_final_response.prefix)
            or hard_final_envelope["semantic_errors"]
            != ["semantic:output-capture-hard-limit"]
            or (
                hard_final_state
                / "objects"
                / "sha256"
                / hard_final_pointer["envelope_sha256"]
                / "payload"
                / "final-response.bin"
            ).exists()
            or (hard_final_state / "slots" / "slot-invalid" / "seal-failure.json").exists()
            or synthetic_verify(hard_final_state)["state_valid"] is not True
        ):
            raise AssertionError("hard-cap final response did not seal canonically")

        entry_cap_state = temporary_root / "entry-cap-state"
        entry_cap_output = temporary_root / "entry-cap-workspace" / "output"
        entry_cap_lease = synthetic_lease(
            "slot-invalid",
            "entry-cap-agent",
            entry_cap_output,
            lease_state=entry_cap_state,
        )
        (entry_cap_output / "report.md").write_bytes(b"{}\n")
        for index in range(MAX_OUTPUT_CAPTURE_ENTRIES):
            (entry_cap_output / f"extra-{index:04d}").touch()
        entry_cap_pointer = synthetic_seal(
            entry_cap_state,
            "slot-invalid",
            entry_cap_lease["lease_token"],
            "entry-cap-agent",
            entry_cap_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        entry_cap_envelope = read_json(
            entry_cap_state
            / "objects"
            / "sha256"
            / entry_cap_pointer["envelope_sha256"]
            / "envelope.json"
        )
        if (
            len(entry_cap_envelope["output_entries"]) != 1
            or entry_cap_envelope["output_entries"][0]["kind"] != "capture-limit"
            or "capture-limit:entry-count" not in entry_cap_envelope["violations"]
            or entry_cap_pointer["semantic_valid"] is not False
            or synthetic_verify(entry_cap_state)["state_valid"] is not True
            or (entry_cap_state / "slots" / "slot-invalid" / "seal-failure.json").exists()
        ):
            raise AssertionError("entry-cap output did not terminalize canonically")

        adversarial_tree_state = temporary_root / "adversarial-output-tree-state"
        adversarial_tree_output = (
            temporary_root / "adversarial-output-tree-workspace" / "output"
        )
        adversarial_tree_lease = synthetic_lease(
            "slot-one",
            "adversarial-output-tree-agent",
            adversarial_tree_output,
            lease_state=adversarial_tree_state,
        )
        (adversarial_tree_output / "report.md").write_text(
            "synthetic report\n", encoding="utf-8"
        )
        deep_directories: list[Path] = []
        deep_cursor = adversarial_tree_output
        for _index in range(1050):
            deep_cursor = deep_cursor / "d"
            deep_cursor.mkdir()
            deep_directories.append(deep_cursor)
        long_directories: list[Path] = []
        long_cursor = adversarial_tree_output
        for index in range(20):
            long_cursor = long_cursor / (f"p{index:02d}-" + "x" * 170)
            long_cursor.mkdir()
            long_directories.append(long_cursor)
        long_file = long_cursor / "long-path-output.txt"
        long_file.write_bytes(b"long path payload\n")
        adversarial_tree_pointer = synthetic_seal(
            adversarial_tree_state,
            "slot-one",
            adversarial_tree_lease["lease_token"],
            "adversarial-output-tree-agent",
            adversarial_tree_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        adversarial_tree_envelope = read_json(
            adversarial_tree_state
            / "objects"
            / "sha256"
            / adversarial_tree_pointer["envelope_sha256"]
            / "envelope.json"
        )
        if (
            adversarial_tree_pointer["format_valid"] is not False
            or len(adversarial_tree_envelope["output_entries"]) != 1
            or adversarial_tree_envelope["output_entries"][0]["kind"]
            != "capture-limit"
            or "capture-limit:path-bytes"
            not in adversarial_tree_envelope["violations"]
            or synthetic_verify(adversarial_tree_state)["state_valid"] is not True
            or (
                adversarial_tree_state
                / "slots"
                / "slot-one"
                / "seal-failure.json"
            ).exists()
        ):
            raise AssertionError(
                "deep or workspace-only-long output path stranded canonical sealing"
            )
        long_file.unlink()
        for directory in reversed(long_directories):
            directory.rmdir()
        for directory in reversed(deep_directories):
            directory.rmdir()

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
        if synthetic_seal(
            state,
            "slot-one",
            lease["lease_token"],
            "agent-one",
            output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        ) != pointer:
            raise AssertionError("same-argument canonical seal recovery drifted")
        for symlink_component in ("object", "sha256", "objects"):
            symlink_state = temporary_root / (
                f"canonical-{symlink_component}-symlink-state"
            )
            shutil.copytree(state, symlink_state)
            object_path = (
                symlink_state
                / "objects"
                / "sha256"
                / pointer["envelope_sha256"]
            )
            component = {
                "object": object_path,
                "sha256": object_path.parent,
                "objects": object_path.parent.parent,
            }[symlink_component]
            displaced = component.with_name(
                f".{component.name}-{symlink_component}-symlink-target"
            )
            os.chmod(component.parent, 0o700)
            component.rename(displaced)
            component.symlink_to(displaced, target_is_directory=True)
            try:
                synthetic_seal(
                    symlink_state,
                    "slot-one",
                    lease["lease_token"],
                    "agent-one",
                    output,
                    b"report.md\n",
                    "returned",
                    0,
                    {"synthetic": True},
                )
            except ProtocolError as error:
                if "canonical object chain" not in str(error):
                    raise AssertionError(
                        "canonical seal retry rejected a symlinked object "
                        f"chain for the wrong reason: {symlink_component}"
                    ) from error
            else:
                raise AssertionError(
                    "canonical seal retry accepted a symlinked object "
                    f"chain: {symlink_component}"
                )
        try:
            synthetic_lease("slot-one", "agent-one", output)
        except LeaseAlreadyExists:
            pass
        else:
            raise AssertionError("a sealed assignment was reacquired")
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
                        production_static_root=RUN,
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
        except (CanonicalAlreadySealed, TerminalAlreadyClaimed):
            pass
        else:
            raise AssertionError("canonical envelope was replaced")

        invalid_output = temporary_root / "workspace-invalid" / "output"
        invalid_lease = synthetic_lease("slot-invalid", "agent-invalid", invalid_output)
        (invalid_output / "extra-empty-directory").mkdir()
        (invalid_output / "report.md").write_text(
            deeply_nested_json, encoding="utf-8"
        )
        invalid_pointer = synthetic_seal(
            state,
            "slot-invalid",
            invalid_lease["lease_token"],
            "agent-invalid",
            invalid_output,
            b"report.md\n",
            "returned",
            0,
            {"synthetic": True},
        )
        assert invalid_pointer["format_valid"] is False
        assert invalid_pointer["semantic_valid"] is False
        invalid_envelope = read_json(
            state
            / "objects"
            / "sha256"
            / invalid_pointer["envelope_sha256"]
            / "envelope.json"
        )
        assert "unexpected-directory:extra-empty-directory" in invalid_envelope["violations"]
        assert any(
            "nesting limit" in error
            for error in invalid_envelope["semantic_errors"]
        )

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
            except (CanonicalAlreadySealed, TerminalAlreadyClaimed):
                return "lost"

        with ThreadPoolExecutor(max_workers=2) as pool:
            race_results = sorted(pool.map(race_seal, ("one", "two")))
        assert race_results == ["lost", "won"]

        recovery_output = temporary_root / "workspace-recovery" / "output"
        recovery_lease = synthetic_lease(
            "slot-recovery", "agent-recovery", recovery_output
        )
        stale_seal_stage = (
            state
            / "objects"
            / "sha256"
            / f".stage-{recovery_lease['attempt_id']}-{'f' * 24}"
        )
        durable_mkdir(stale_seal_stage)
        (stale_seal_stage / "stale.json").write_text(
            "{}\n", encoding="utf-8"
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
        if stale_seal_stage.exists() or stale_seal_stage.is_symlink():
            raise AssertionError("stale pre-claim seal stage survived a retry")
        incomplete = synthetic_verify(state)
        recovery_row = next(
            row for row in incomplete["slots"] if row["slot_id"] == "slot-recovery"
        )
        assert recovery_row["status"] == "TERMINAL_CLAIMED_INCOMPLETE"
        recovery_stages_before_wrong_retry = sorted(
            (path.name, byte_tree_digest(path))
            for path in (state / "objects" / "sha256").iterdir()
            if path.name.startswith(f".stage-{recovery_lease['attempt_id']}-")
        )
        if len(recovery_stages_before_wrong_retry) != 1:
            raise AssertionError("terminal-claim crash lacks its exact recovery stage")
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
                {"synthetic": True, "changed_retry": True},
            )
        except TerminalAlreadyClaimed:
            pass
        else:
            raise AssertionError("changed terminal-claim recovery arguments were accepted")
        recovery_stages_after_wrong_retry = sorted(
            (path.name, byte_tree_digest(path))
            for path in (state / "objects" / "sha256").iterdir()
            if path.name.startswith(f".stage-{recovery_lease['attempt_id']}-")
        )
        if (
            recovery_stages_after_wrong_retry
            != recovery_stages_before_wrong_retry
            or (
                state / "slots" / "slot-recovery" / "seal-failure.json"
            ).exists()
        ):
            raise AssertionError(
                "mismatched terminal-claim retry poisoned the valid recovery state"
            )
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
        assert verified["complete"] is False
        assert verified["state_valid"] is True
        assert verified["outcome"] == "IN_PROGRESS"
        assert verified["all_started_attempts_terminal"] is True
        assert verified["all_outputs_valid"] is False
    print(
        "DRAFT protocol self-test passed "
        "(atoms, closed rules, A-O scoring, adjudication union/merge, DAGs, gates, lease, envelope, CAS)"
    )


def production_runtime_self_test() -> None:
    """Exercise complete minimum and maximum staged production runtimes."""

    integration = trusted_integration_module()

    def discard_temporary_tree(root: Path) -> None:
        if not root.exists():
            return
        for directory, directory_names, _file_names in os.walk(
            root, topdown=True, followlinks=False
        ):
            directory_names.sort()
            directory_path = Path(directory)
            if directory_path.is_symlink():
                raise AssertionError("runtime self-test workspace contains a symlink")
            os.chmod(directory_path, 0o700)
        shutil.rmtree(root)

    def tree_byte_mode_identity(root: Path) -> list[tuple[str, str, int, str | None]]:
        records: list[tuple[str, str, int, str | None]] = []
        for path in (root, *sorted(root.rglob("*"), key=lambda item: item.as_posix())):
            relative = "." if path == root else path.relative_to(root).as_posix()
            if path.is_symlink() or not (path.is_dir() or path.is_file()):
                raise AssertionError(f"runtime identity tree has unsupported entry: {relative}")
            records.append(
                (
                    relative,
                    "directory" if path.is_dir() else "file",
                    stat.S_IMODE(path.lstat().st_mode),
                    sha256(path.read_bytes()) if path.is_file() else None,
                )
            )
        return records

    def clean_workspace(lease: dict[str, Any]) -> None:
        discard_temporary_tree(Path(lease["attempt_root"]).parent)

    def seal_output(
        bundle: Path,
        commitment: Path,
        lease: dict[str, Any],
        output: bytes,
        *,
        expect_valid: bool = True,
        output_root_mode: int | None = None,
    ) -> dict[str, Any]:
        launch = load_bound_launch(lease)
        output_path = Path(lease["attempt_root"]) / Path(
            *PurePosixPath(launch["output_path"]).parts
        )
        output_path.parent.mkdir(parents=True, exist_ok=True)
        output_path.write_bytes(output)
        if output_root_mode is not None:
            os.chmod(Path(lease["attempt_root"]), output_root_mode)
        pointer = seal_production_attempt(
            bundle,
            commitment,
            lease["slot_id"],
            lease["lease_token"],
            lease["agent_id"],
            (launch["output_path"] + "\n").encode("utf-8"),
            "RETURNED",
            0,
            {"runtime_self_test": True},
        )
        if expect_valid and (
            pointer["format_valid"] is not True
            or pointer["semantic_valid"] is not True
        ):
            raise AssertionError(
                f"runtime self-test output was not valid: {lease['slot_id']}"
            )
        if not expect_valid and pointer["semantic_valid"] is not False:
            raise AssertionError(
                f"runtime self-test invalid output passed semantics: {lease['slot_id']}"
            )
        if output_root_mode is not None:
            if (
                stat.S_IMODE(Path(lease["attempt_root"]).lstat().st_mode)
                != output_root_mode
            ):
                raise AssertionError(
                    "production sealing did not restore the agent-selected output-root mode"
                )
            os.chmod(Path(lease["attempt_root"]), 0o700)
        clean_workspace(lease)
        return pointer

    def clean_direct_score(packet: dict[str, Any]) -> dict[str, Any]:
        mode = packet["mode"]
        scorer = packet["scorer_id"]
        atoms = packet_json_file(
            packet["packet_tree"], SCORE_RESOURCE_PATHS["atom_manifest"]
        )
        rules = packet_json_file(
            packet["packet_tree"], SCORE_RESOURCE_PATHS["defect_rules"]
        )
        packet_reports = {row["label"]: row for row in packet["reports"]}
        return {
            "schema_version": 1,
            "status": "DIRECT-SCORE",
            "mode": mode,
            "scorer_id": scorer,
            "claim": f"{mode}-{scorer}",
            "input_packet_sha256": sha256(canonical_json_bytes(packet)),
            "reports": [
                {
                    "label": label,
                    "atoms": [
                        {
                            "id": atom["id"],
                            "direct_decision": "PASS",
                            "evidence": "Mechanical runtime-path proof-quality fixture.",
                        }
                        for atom in atoms["atoms"]
                    ],
                    "hard_errors": [
                        {
                            "id": rule_id,
                            "present": (
                                packet_reports[label]["gh12_forced_present"]
                                if rule_id == "GH12"
                                else False
                            ),
                            "evidence": "Mechanical runtime-path defect fixture.",
                        }
                        for rule_id in hard_error_ids(rules, mode)
                    ],
                    "global_defects": [
                        {
                            "id": rule_id,
                            "present": False,
                            "evidence": "Mechanical runtime-path global fixture.",
                        }
                        for rule_id in global_defect_ids(rules)
                    ],
                    "novel_findings": [],
                }
                for label in packet["labels_in_order"]
            ],
        }

    def clean_consistency_review(
        packet: dict[str, Any], reviewer: str, *, force_challenge: bool = False
    ) -> dict[str, Any]:
        atoms = packet_json_file(
            packet["packet_tree"], "resources/atom-manifest.json"
        )
        rules = packet_json_file(
            packet["packet_tree"], "resources/defect-rules.json"
        )
        atom_fields, defect_fields = atom_and_defect_fields(atoms, rules)
        mode = packet["mode"]
        review = {
            "schema_version": 1,
            "status": "CONSISTENCY-REVIEW",
            "mode": mode,
            "reviewer_id": reviewer,
            "claim": f"{mode}-{reviewer}",
            "input_packet_sha256": sha256(canonical_json_bytes(packet)),
            "labels_reviewed": list(LABELS),
            "atom_family_attestations": [
                {
                    "field": field,
                    "labels_reviewed": list(LABELS),
                    "evidence": "Mechanical A-O atom-family consistency fixture.",
                }
                for field in atom_fields
            ],
            "defect_family_attestations": [
                {
                    "field": field,
                    "labels_reviewed": list(LABELS),
                    "evidence": "Mechanical A-O defect-family consistency fixture.",
                }
                for field in defect_fields
            ],
            "challenges": [],
            "novel_classifications": [
                {
                    "normalized_id": assertion["id"],
                    "category": "INVALID_ASSERTION",
                    "evidence": "Mechanical normalized-assertion routing fixture.",
                }
                for assertion in packet["novel_assertions"]
            ],
        }
        if force_challenge:
            review["challenges"].append(
                {
                    "label": LABELS[0],
                    "field": atom_fields[0],
                    "proposed_decision": "FAIL",
                    "evidence": "Mechanical forced adjudication-path fixture.",
                }
            )
        return review

    def clean_adjudication(packet: dict[str, Any]) -> dict[str, Any]:
        resolutions: list[dict[str, str]] = []
        for cell in packet["cells"]:
            field = cell["field"]
            if field.startswith("atom:"):
                decision = "PASS"
            elif field.startswith("novel:"):
                decision = "INVALID_ASSERTION"
            else:
                decision = "ABSENT"
            resolutions.append(
                {
                    "cell_id": cell["cell_id"],
                    "decision": decision,
                    "evidence": "Mechanical runtime adjudication fixture.",
                }
            )
        return {
            "schema_version": 1,
            "status": "ADJUDICATED",
            "mode": packet["mode"],
            "packet_sha256": sha256(canonical_json_bytes(packet)),
            "resolutions": resolutions,
        }

    def clean_materiality_review(
        packet: dict[str, Any], reviewer: str, *, force_finding: bool = False
    ) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "status": "MATERIALITY-REVIEW",
            "reviewer_id": reviewer,
            "input_packet_sha256": sha256(canonical_json_bytes(packet)),
            "scope_attestations": [
                {
                    "scope": scope,
                    "complete": True,
                    "evidence": "Mechanical exhaustive materiality-scope fixture.",
                }
                for scope in MATERIALITY_SCOPES
            ],
            "findings": (
                [
                    {
                        "id": f"{reviewer}-F1",
                        "scope": "HARNESS_PROTOCOL",
                        "description": "Mechanical single-reviewer materiality fixture.",
                        "evidence": "Mechanical runtime materiality finding fixture.",
                        "proposed_blocking": False,
                    }
                ]
                if force_finding
                else []
            ),
        }

    def clean_materiality_adjudication(packet: dict[str, Any]) -> dict[str, Any]:
        return {
            "schema_version": 1,
            "status": "ADJUDICATED",
            "packet_sha256": sha256(canonical_json_bytes(packet)),
            "resolutions": [
                {
                    "cell_id": cell["cell_id"],
                    "decision": "NOT_BLOCKING",
                    "evidence": "Mechanical runtime materiality resolution fixture.",
                }
                for cell in packet["cells"]
            ],
        }

    with tempfile.TemporaryDirectory(prefix="v5-production-runtime-") as temp_text:
        temporary_root = Path(temp_text)
        # The mechanical fixture intentionally reruns the verbose semantic
        # validators for every source/snapshot receipt.  Keep library output
        # out of this runtime test while preserving every validation call.
        with open(os.devnull, "w", encoding="utf-8") as quiet_output:
            with contextlib.redirect_stdout(quiet_output):
                bundle, commitment = integration[
                    "_build_mechanical_production_bundle_for_protocol_self_test"
                ](
                    temporary_root / "static-fixture",
                    synthetic_capability=integration["_SYNTHETIC_CAPABILITY"],
                )
        captured = load_verified_static_bundle_with_review_evidence(
            bundle, commitment
        )
        cached_documents = load_ready_generated_documents(bundle)
        cached_prepare = run_trusted_module(
            "prepare.py", "v5_production_runtime_cached_prepare"
        )
        cached_word_count = run_trusted_module(
            "word_count.py", "v5_production_runtime_cached_word_count"
        )
        cached_static_context = load_aggregation_static_context(
            captured[0], captured[1], captured[2], captured[3]
        )
        cached_documents_baseline = copy.deepcopy(cached_documents)
        cached_static_context_baseline = copy.deepcopy(cached_static_context)
        captured_baseline = copy.deepcopy(captured)
        original_load = globals()["load_verified_static_bundle"]
        original_load_with_evidence = globals()[
            "load_verified_static_bundle_with_review_evidence"
        ]
        original_load_documents = globals()["load_ready_generated_documents"]
        original_load_static_context = globals()["load_aggregation_static_context"]
        original_run_trusted_module = globals()["run_trusted_module"]
        original_trusted_integration_module = globals()["trusted_integration_module"]

        def require_test_paths(
            static_root: Path, external_commitment_path: Path | None
        ) -> None:
            if (
                Path(os.path.abspath(os.fspath(static_root))) != bundle
                or external_commitment_path is None
                or Path(os.path.abspath(os.fspath(external_commitment_path)))
                != commitment
            ):
                raise AssertionError("runtime self-test verifier received the wrong roots")

        def cached_load(
            static_root: Path, external_commitment_path: Path | None = None
        ) -> tuple[Path, dict[str, Any], frozenset[str]]:
            require_test_paths(static_root, external_commitment_path)
            return captured[:3]

        def cached_load_with_evidence(
            static_root: Path, external_commitment_path: Path | None = None
        ) -> tuple[Path, dict[str, Any], frozenset[str], dict[str, Any]]:
            require_test_paths(static_root, external_commitment_path)
            return captured

        def cached_load_documents(static_root: Path) -> dict[str, Any]:
            if Path(os.path.abspath(os.fspath(static_root))) != bundle:
                raise AssertionError(
                    "runtime self-test document loader received the wrong root"
                )
            return cached_documents

        def cached_load_static_context(
            root: Path,
            static_lock: dict[str, Any],
            reviewer_ids: frozenset[str],
            review_evidence: dict[str, Any],
        ) -> dict[str, Any]:
            if (
                root != captured[0]
                or static_lock != captured[1]
                or reviewer_ids != captured[2]
                or review_evidence != captured[3]
            ):
                raise AssertionError(
                    "runtime self-test static-context loader received a different capture"
                )
            return cached_static_context

        def cached_run_trusted_module(name: str, run_name: str) -> dict[str, Any]:
            del run_name
            if name == "integrate.py":
                return integration
            if name == "prepare.py":
                return cached_prepare
            if name == "word_count.py":
                return cached_word_count
            raise AssertionError(f"unexpected trusted module request: {name}")

        globals()["load_verified_static_bundle"] = cached_load
        globals()[
            "load_verified_static_bundle_with_review_evidence"
        ] = cached_load_with_evidence
        globals()["load_ready_generated_documents"] = cached_load_documents
        globals()["load_aggregation_static_context"] = cached_load_static_context
        globals()["run_trusted_module"] = cached_run_trusted_module
        globals()["trusted_integration_module"] = lambda: integration
        try:
            def reject_prevalidation_loader(*_args: Any, **_kwargs: Any) -> Any:
                raise AssertionError(
                    "invalid production request reached static-bundle loading"
                )

            globals()["load_verified_static_bundle"] = reject_prevalidation_loader
            globals()[
                "load_verified_static_bundle_with_review_evidence"
            ] = reject_prevalidation_loader
            try:
                invalid_production_requests: tuple[
                    tuple[str, Callable[[], Any]], ...
                ] = (
                    (
                        "aggregation actor",
                        lambda: _advance_aggregation_under_custody(
                            bundle, commitment, "short", publish=True
                        ),
                    ),
                    (
                        "aggregation publish authority",
                        lambda: _advance_aggregation_under_custody(
                            bundle,
                            commitment,
                            "runtime-coordinator-0001",
                            publish=1,  # type: ignore[arg-type]
                        ),
                    ),
                    (
                        "evaluator assignment",
                        lambda: _acquire_evaluator_lease_under_custody(
                            bundle,
                            commitment,
                            str(temporary_root / "redirected-slot"),
                            "runtime-evaluator-0001",
                        ),
                    ),
                    (
                        "report agent",
                        lambda: _acquire_report_lease_under_custody(
                            bundle, commitment, "r001", "short"
                        ),
                    ),
                    (
                        "seal slot",
                        lambda: _seal_production_attempt_under_custody(
                            bundle,
                            commitment,
                            str(temporary_root / "redirected-slot"),
                            "0" * 64,
                            "runtime-sealer-0001",
                            None,
                            "RETURNED",
                            0,
                            {},
                        ),
                    ),
                )
                for label, operation in invalid_production_requests:
                    try:
                        operation()
                    except ProtocolError:
                        pass
                    else:
                        raise AssertionError(
                            f"invalid production {label} request was accepted"
                        )
            finally:
                globals()["load_verified_static_bundle"] = cached_load
                globals()[
                    "load_verified_static_bundle_with_review_evidence"
                ] = cached_load_with_evidence
            coordinator = "runtime-coordinator-0001"
            progress = advance_aggregation(
                bundle, commitment, coordinator
            )
            if (
                progress["status"] != "WAITING"
                or progress["current_stage"] != "reports"
                or progress["leaseable_assignments"]
                != [f"r{index:03d}" for index in range(1, 121)]
            ):
                raise AssertionError("initial aggregation progress is not exact")
            mismatched_residue = (
                bundle
                / "runtime"
                / "state"
                / "aggregation"
                / "derived"
                / f"{AGGREGATION_PENDING_STAGE_PREFIX}01-report-products"
            )
            mismatched_residue.mkdir(parents=True)
            (mismatched_residue / "private-data").write_bytes(
                b"must survive a mismatched coordinator request\n"
            )
            try:
                advance_aggregation(
                    bundle, commitment, "runtime-coordinator-0002"
                )
            except ProtocolError:
                pass
            else:
                raise AssertionError("aggregation coordinator identity drift was accepted")
            if not mismatched_residue.is_dir():
                raise AssertionError(
                    "mismatched coordinator request deleted private recovery residue"
                )
            progress = advance_aggregation(bundle, commitment, coordinator)
            if mismatched_residue.exists() or mismatched_residue.is_symlink():
                raise AssertionError(
                    "matching coordinator request did not recover private residue"
                )
            try:
                acquire_report_lease(
                    bundle, commitment, "r001", coordinator
                )
            except ProtocolError:
                pass
            else:
                raise AssertionError("aggregation coordinator acquired a report lease")
            if (bundle / "runtime" / "state" / "slots" / "r001").exists():
                raise AssertionError("rejected coordinator lease mutated report state")
            initial_state = verify_production_state(bundle, commitment)
            if initial_state["state_valid"] is not True or initial_state["complete"]:
                raise AssertionError("coordinator-only runtime state is invalid")

            first_report_lease: dict[str, Any] | None = None
            first_report_pointer: dict[str, Any] | None = None
            for index in range(1, 121):
                run_id = f"r{index:03d}"
                lease = acquire_report_lease(
                    bundle,
                    commitment,
                    run_id,
                    f"runtime-report-{index:04d}",
                )
                sealed_pointer = seal_output(
                    bundle,
                    commitment,
                    lease,
                    (
                        "Reviewed the supplied Rust target and reconstructed its "
                        "local safety argument.\n"
                    ).encode("utf-8"),
                    output_root_mode=(
                        0o000 if index == 1 else 0o400 if index == 2 else None
                    ),
                )
                if index == 1:
                    first_report_lease = copy.deepcopy(lease)
                    first_report_pointer = sealed_pointer

            progress = advance_aggregation(bundle, commitment, coordinator)
            expected_scorers = sorted(
                f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS
            )
            if (
                progress["current_stage"] != "01-report-products"
                or progress["leaseable_assignments"] != expected_scorers
            ):
                raise AssertionError("Stage 01 did not expose the exact scorer set")

            state_root = bundle / "runtime" / "state"
            stage_01_checkpoint = temporary_root / "stage-01-state-checkpoint"
            shutil.copytree(state_root, stage_01_checkpoint)
            original_acquire_lease = globals()["acquire_lease"]
            evaluator_fault_fired = [False]

            def faulting_production_acquire(*args: Any, **kwargs: Any) -> dict[str, Any]:
                if not evaluator_fault_fired[0]:
                    evaluator_fault_fired[0] = True
                    kwargs["fault_after"] = "lease-cas"
                return original_acquire_lease(*args, **kwargs)

            globals()["acquire_lease"] = faulting_production_acquire
            try:
                try:
                    acquire_evaluator_lease(
                        bundle,
                        commitment,
                        expected_scorers[0],
                        "runtime-terminal-scorer-0001",
                    )
                except InjectedFault:
                    pass
                else:
                    raise AssertionError(
                        "production evaluator wrapper lease-CAS fault did not fire"
                    )
            finally:
                globals()["acquire_lease"] = original_acquire_lease
            if not evaluator_fault_fired[0]:
                raise AssertionError("production evaluator lease fault seam was bypassed")
            for index, assignment in enumerate(expected_scorers, start=1):
                lease = acquire_evaluator_lease(
                    bundle,
                    commitment,
                    assignment,
                    f"runtime-terminal-scorer-{index:04d}",
                )
                packet = load_bound_input_packet(lease)
                seal_output(
                    bundle,
                    commitment,
                    lease,
                    (
                        canonical_json_bytes(clean_direct_score(packet))
                        if index != 1
                        else canonical_json_bytes({})
                    ),
                    expect_valid=index != 1,
                )
            terminal_progress = advance_aggregation(
                bundle, commitment, coordinator
            )
            if (
                terminal_progress["status"] != "TERMINAL-FAILURE"
                or terminal_progress["current_stage"] != "02-scorer-products"
                or terminal_progress["leaseable_assignments"]
                or terminal_progress["pending_assignments"]
            ):
                raise AssertionError("invalid scorer phase did not terminalize exactly")
            if first_report_lease is None or first_report_pointer is None:
                raise AssertionError("first report retry fixture was not retained")
            first_report_launch = load_bound_launch(first_report_lease)
            if seal_production_attempt(
                bundle,
                commitment,
                first_report_lease["slot_id"],
                first_report_lease["lease_token"],
                first_report_lease["agent_id"],
                (first_report_launch["output_path"] + "\n").encode("utf-8"),
                "RETURNED",
                0,
                {"runtime_self_test": True},
            ) != first_report_pointer:
                raise AssertionError(
                    "published canonical seal did not dominate later aggregation failure"
                )
            terminal_state = verify_production_state(bundle, commitment)
            if (
                terminal_state["state_valid"] is not True
                or terminal_state["complete"] is not True
                or terminal_state["outcome"] != "ERROR"
                or terminal_state["all_outputs_valid"] is not False
                or len(terminal_state["slots"]) != 136
                or aggregation_status(bundle, commitment) != terminal_progress
            ):
                raise AssertionError("authenticated terminal runtime state is inconsistent")
            try:
                acquire_evaluator_lease(
                    bundle,
                    commitment,
                    "m1",
                    "runtime-terminal-rejected-0001",
                )
            except ProtocolError:
                pass
            else:
                raise AssertionError("terminal aggregation exposed a later evaluator lease")
            for terminal_consumer in (
                derive_aggregate_context,
                evaluate_bound_gates,
            ):
                try:
                    terminal_consumer(bundle, commitment)
                except ProtocolError as error:
                    if "authenticated terminal error" not in str(error):
                        raise AssertionError(
                            "terminal aggregate consumer failed for the wrong reason"
                        ) from error
                else:
                    raise AssertionError("terminal aggregation masqueraded as a final result")
            discard_temporary_tree(state_root)
            shutil.copytree(stage_01_checkpoint, state_root)
            if aggregation_status(bundle, commitment) != progress:
                raise AssertionError("Stage 01 checkpoint did not restore byte-exact progress")

            for index, assignment in enumerate(expected_scorers, start=1):
                lease = acquire_evaluator_lease(
                    bundle,
                    commitment,
                    assignment,
                    f"runtime-scorer-{index:04d}",
                )
                packet = load_bound_input_packet(lease)
                seal_output(
                    bundle,
                    commitment,
                    lease,
                    canonical_json_bytes(clean_direct_score(packet)),
                )

            progress = advance_aggregation(bundle, commitment, coordinator)
            expected_consistency = sorted(
                f"{mode}-{reviewer}"
                for mode in MODES
                for reviewer in CONSISTENCY_REVIEWERS
            )
            if (
                progress["current_stage"] != "02-scorer-products"
                or progress["leaseable_assignments"] != expected_consistency
            ):
                raise AssertionError(
                    "Stage 02 did not expose the exact consistency-review set"
                )
            stage_02_progress = copy.deepcopy(progress)
            stage_02_checkpoint = temporary_root / "stage-02-state-checkpoint"
            shutil.copytree(state_root, stage_02_checkpoint)

            for index, assignment in enumerate(expected_consistency, start=1):
                reviewer = assignment.rsplit("-", 1)[1]
                lease = acquire_evaluator_lease(
                    bundle,
                    commitment,
                    assignment,
                    f"runtime-consistency-{index:04d}",
                )
                packet = load_bound_input_packet(lease)
                seal_output(
                    bundle,
                    commitment,
                    lease,
                    canonical_json_bytes(
                        clean_consistency_review(packet, reviewer)
                    ),
                )

            progress = advance_aggregation(bundle, commitment, coordinator)
            if (
                progress["current_stage"] != "04-score-products"
                or progress["leaseable_assignments"] != ["m1", "m2"]
                or any(
                    assignment.endswith("-a1")
                    for assignment in progress["sealed_assignments"]
                )
            ):
                raise AssertionError(
                    "empty mode adjudication did not deterministically skip every a1"
                )

            for index, reviewer in enumerate(MATERIALITY_REVIEWERS, start=1):
                lease = acquire_evaluator_lease(
                    bundle,
                    commitment,
                    reviewer,
                    f"runtime-materiality-{index:04d}",
                )
                packet = load_bound_input_packet(lease)
                seal_output(
                    bundle,
                    commitment,
                    lease,
                    canonical_json_bytes(
                        clean_materiality_review(packet, reviewer)
                    ),
                )

            progress = advance_aggregation(bundle, commitment, coordinator)
            if (
                progress["status"] != "COMPLETE"
                or progress["current_stage"] != "final"
                or len(progress["sealed_assignments"]) != 154
                or "ma1" in progress["sealed_assignments"]
                or progress["leaseable_assignments"]
                or progress["pending_assignments"]
            ):
                raise AssertionError("minimum staged runtime did not finish at 154 attempts")
            complete_state_identity = tree_byte_mode_identity(
                bundle / "runtime" / "state"
            )
            stable_progress = advance_aggregation(bundle, commitment, coordinator)
            if stable_progress != progress or aggregation_status(
                bundle, commitment
            ) != progress:
                raise AssertionError("completed aggregation is not byte-stable/idempotent")
            if tree_byte_mode_identity(
                bundle / "runtime" / "state"
            ) != complete_state_identity:
                raise AssertionError("idempotent aggregation mutated the completed tree")
            minimum_state = verify_production_state(bundle, commitment)
            if (
                minimum_state["state_valid"] is not True
                or minimum_state["complete"] is not True
                or len(minimum_state["slots"]) != 154
            ):
                raise AssertionError("minimum production state did not validate exactly")
            minimum_gate_result = evaluate_bound_gates(bundle, commitment)
            minimum_decisions = {
                row["id"]: row["certificate_decision"]
                for row in minimum_gate_result["gates"]
            }
            if any(
                minimum_decisions[gate_id] != "PASS"
                for gate_id in REQUIRED_ROOT_ORDER
                if gate_id.startswith("D-")
            ) or any(
                minimum_decisions[gate_id] != "FAIL"
                for gate_id in ("G-ISOLATION", "G-OUTPUT-FINALIZATION")
            ):
                raise AssertionError("minimum runtime gate outcomes are not exact")
            if tree_byte_mode_identity(state_root) != complete_state_identity:
                raise AssertionError(
                    "minimum read-only verification mutated runtime state"
                )

            discard_temporary_tree(state_root)
            shutil.copytree(stage_02_checkpoint, state_root)
            if aggregation_status(bundle, commitment) != stage_02_progress:
                raise AssertionError("Stage 02 checkpoint did not restore byte-exact progress")

            for index, assignment in enumerate(expected_consistency, start=1):
                reviewer = assignment.rsplit("-", 1)[1]
                lease = acquire_evaluator_lease(
                    bundle,
                    commitment,
                    assignment,
                    f"runtime-max-consistency-{index:04d}",
                )
                packet = load_bound_input_packet(lease)
                seal_output(
                    bundle,
                    commitment,
                    lease,
                    canonical_json_bytes(
                        clean_consistency_review(
                            packet, reviewer, force_challenge=True
                        )
                    ),
                )

            progress = advance_aggregation(bundle, commitment, coordinator)
            expected_adjudicators = sorted(f"{mode}-a1" for mode in MODES)
            if (
                progress["current_stage"] != "03-consistency-products"
                or progress["leaseable_assignments"] != expected_adjudicators
            ):
                raise AssertionError(
                    "Stage 03 did not expose all eight conditional adjudicators"
                )
            for index, assignment in enumerate(expected_adjudicators, start=1):
                lease = acquire_evaluator_lease(
                    bundle,
                    commitment,
                    assignment,
                    f"runtime-adjudicator-{index:04d}",
                )
                packet = load_bound_input_packet(lease)
                if not packet["cells"]:
                    raise AssertionError("conditional adjudicator received an empty packet")
                seal_output(
                    bundle,
                    commitment,
                    lease,
                    canonical_json_bytes(clean_adjudication(packet)),
                )

            progress = advance_aggregation(bundle, commitment, coordinator)
            if (
                progress["current_stage"] != "04-score-products"
                or progress["leaseable_assignments"] != ["m1", "m2"]
            ):
                raise AssertionError("maximum path did not reach materiality review")
            for index, reviewer in enumerate(MATERIALITY_REVIEWERS, start=1):
                lease = acquire_evaluator_lease(
                    bundle,
                    commitment,
                    reviewer,
                    f"runtime-max-materiality-{index:04d}",
                )
                packet = load_bound_input_packet(lease)
                seal_output(
                    bundle,
                    commitment,
                    lease,
                    canonical_json_bytes(
                        clean_materiality_review(
                            packet, reviewer, force_finding=reviewer == "m1"
                        )
                    ),
                )

            progress = advance_aggregation(bundle, commitment, coordinator)
            if (
                progress["current_stage"] != "05-materiality-products"
                or progress["leaseable_assignments"] != ["ma1"]
            ):
                raise AssertionError(
                    "Stage 05 did not expose the conditional materiality adjudicator"
                )
            materiality_adjudicator = acquire_evaluator_lease(
                bundle,
                commitment,
                "ma1",
                "runtime-materiality-adjudicator-0001",
            )
            materiality_packet = load_bound_input_packet(materiality_adjudicator)
            if not materiality_packet["cells"]:
                raise AssertionError("materiality adjudicator received an empty packet")
            seal_output(
                bundle,
                commitment,
                materiality_adjudicator,
                canonical_json_bytes(
                    clean_materiality_adjudication(materiality_packet)
                ),
            )

            progress = advance_aggregation(bundle, commitment, coordinator)
            if (
                progress["status"] != "COMPLETE"
                or progress["current_stage"] != "final"
                or len(progress["sealed_assignments"]) != 163
                or not set(expected_adjudicators).issubset(
                    progress["sealed_assignments"]
                )
                or "ma1" not in progress["sealed_assignments"]
                or progress["leaseable_assignments"]
                or progress["pending_assignments"]
            ):
                raise AssertionError("maximum staged runtime did not finish at 163 attempts")
            complete_state_identity = tree_byte_mode_identity(
                bundle / "runtime" / "state"
            )
        finally:
            globals()["load_verified_static_bundle"] = original_load
            globals()[
                "load_verified_static_bundle_with_review_evidence"
            ] = original_load_with_evidence
            globals()["load_ready_generated_documents"] = original_load_documents
            globals()["load_aggregation_static_context"] = original_load_static_context
            globals()["run_trusted_module"] = original_run_trusted_module
            globals()["trusted_integration_module"] = original_trusted_integration_module
            if (
                cached_documents != cached_documents_baseline
                or cached_static_context != cached_static_context_baseline
                or captured != captured_baseline
            ):
                raise AssertionError(
                    "production runtime self-test mutated its authenticated cache"
                )

        final_state = verify_production_state(bundle, commitment)
        if (
            final_state["state_valid"] is not True
            or final_state["complete"] is not True
            or len(final_state["slots"]) != 163
        ):
            raise AssertionError("final production state did not validate exactly")
        gate_result = evaluate_bound_gates(bundle, commitment)
        decisions = {
            row["id"]: row["certificate_decision"] for row in gate_result["gates"]
        }
        if any(
            decisions[gate_id] != "PASS"
            for gate_id in REQUIRED_ROOT_ORDER
            if gate_id.startswith("D-")
        ) or any(
            decisions[gate_id] != "FAIL"
            for gate_id in ("G-ISOLATION", "G-OUTPUT-FINALIZATION")
        ):
            raise AssertionError("maximum runtime gate outcomes are not exact")
        if tree_byte_mode_identity(
            bundle / "runtime" / "state"
        ) != complete_state_identity:
            raise AssertionError("read-only final verification mutated runtime state")
        final_root = bundle / "runtime" / "state" / "aggregation" / "final"
        if len(list((final_root / "integration-receipts").glob("*.json"))) != 8:
            raise AssertionError("final aggregation lacks the exact eight receipts")
    print(
        "PRODUCTION staged runtime self-test passed "
        "(154-attempt minimum and 163-attempt maximum, six stages)"
    )


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    subcommands = parser.add_subparsers(dest="command", required=True)
    subcommands.add_parser("verify-draft")
    subcommands.add_parser("self-test")
    subcommands.add_parser("self-test-production-runtime")
    subcommands.add_parser("validate-integration-spec")
    derive_aggregate = subcommands.add_parser("derive-aggregate-context")
    derive_aggregate.add_argument("--static-root", type=Path, required=True)
    derive_aggregate.add_argument("--external-commitment", type=Path, required=True)
    advance = subcommands.add_parser("advance-aggregation")
    advance.add_argument("--static-root", type=Path, required=True)
    advance.add_argument("--external-commitment", type=Path, required=True)
    advance.add_argument("--coordinator-actor", required=True)
    status = subcommands.add_parser("aggregation-status")
    status.add_argument("--static-root", type=Path, required=True)
    status.add_argument("--external-commitment", type=Path, required=True)
    bound_gates = subcommands.add_parser("evaluate-bound-gates")
    bound_gates.add_argument("--static-root", type=Path, required=True)
    bound_gates.add_argument("--external-commitment", type=Path, required=True)
    evaluator_launch = subcommands.add_parser("build-evaluator-launch")
    evaluator_launch.add_argument("--static-root", type=Path, required=True)
    evaluator_launch.add_argument("--external-commitment", type=Path, required=True)
    evaluator_launch.add_argument("--assignment", required=True)
    report_lease = subcommands.add_parser("lease-report")
    report_lease.add_argument("--static-root", type=Path, required=True)
    report_lease.add_argument("--external-commitment", type=Path, required=True)
    report_lease.add_argument("--run-id", required=True)
    report_lease.add_argument("--agent", required=True)
    evaluator_lease = subcommands.add_parser("lease-evaluator")
    evaluator_lease.add_argument("--static-root", type=Path, required=True)
    evaluator_lease.add_argument("--external-commitment", type=Path, required=True)
    evaluator_lease.add_argument("--assignment", required=True)
    evaluator_lease.add_argument("--agent", required=True)
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
    seal = subcommands.add_parser("seal-attempt")
    seal.add_argument("--static-root", type=Path, required=True)
    seal.add_argument("--external-commitment", type=Path, required=True)
    seal.add_argument("--slot", required=True)
    seal.add_argument("--agent", required=True)
    seal.add_argument("--lease-token", required=True)
    seal.add_argument("--final-response", type=Path)
    seal.add_argument("--process-disposition", required=True)
    seal.add_argument("--process-exit-code", type=int)
    seal.add_argument("--metadata", type=Path, required=True)
    verify = subcommands.add_parser("verify-state")
    verify.add_argument("--static-root", type=Path, required=True)
    verify.add_argument("--external-commitment", type=Path, required=True)
    args = parser.parse_args()
    if args.command == "verify-draft":
        verify_draft()
    elif args.command == "self-test":
        verify_draft()
        self_test()
    elif args.command == "self-test-production-runtime":
        production_runtime_self_test()
    elif args.command == "derive-aggregate-context":
        sys.stdout.buffer.write(
            canonical_json_bytes(
                derive_aggregate_context(args.static_root, args.external_commitment)
            )
        )
    elif args.command == "advance-aggregation":
        print(
            pretty_json(
                advance_aggregation(
                    args.static_root,
                    args.external_commitment,
                    args.coordinator_actor,
                )
            ),
            end="",
        )
    elif args.command == "aggregation-status":
        print(
            pretty_json(
                aggregation_status(
                    args.static_root,
                    args.external_commitment,
                )
            ),
            end="",
        )
    elif args.command == "evaluate-bound-gates":
        print(
            pretty_json(
                evaluate_bound_gates(args.static_root, args.external_commitment)
            ),
            end="",
        )
    elif args.command == "build-evaluator-launch":
        launch = build_production_evaluator_launch(
            args.static_root,
            args.external_commitment,
            args.assignment,
        )
        sys.stdout.buffer.write(canonical_json_bytes(launch))
    elif args.command == "lease-report":
        print(
            pretty_json(
                acquire_report_lease(
                    args.static_root,
                    args.external_commitment,
                    args.run_id,
                    args.agent,
                )
            ),
            end="",
        )
    elif args.command == "lease-evaluator":
        print(
            pretty_json(
                acquire_evaluator_lease(
                    args.static_root,
                    args.external_commitment,
                    args.assignment,
                    args.agent,
                )
            ),
            end="",
        )
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
    elif args.command == "seal-attempt":
        response = (
            read_bounded_final_response(
                args.final_response,
                MAX_ENVELOPE_CAPTURE_BYTES,
                "seal final-response input",
            )
            if args.final_response is not None
            else None
        )
        print(
            pretty_json(
                seal_production_attempt(
                    args.static_root,
                    args.external_commitment,
                    args.slot,
                    args.lease_token,
                    args.agent,
                    response,
                    args.process_disposition,
                    args.process_exit_code,
                    read_json(args.metadata),
                )
            ),
            end="",
        )
    else:
        print(
            pretty_json(
                verify_production_state(
                    args.static_root,
                    args.external_commitment,
                )
            ),
            end="",
        )


if __name__ == "__main__":
    main()
