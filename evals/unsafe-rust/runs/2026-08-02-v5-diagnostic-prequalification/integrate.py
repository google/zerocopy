#!/usr/bin/env python3
"""Prepare, review, finalize, and verify a V5 prelaunch static bundle.

Production integration has two independently reviewed boundaries. First,
``prepare-source-review`` constructs an immutable SOURCE-REVIEW-CANDIDATE from
the DRAFT semantic templates and exact theorem inputs. Three independent
source-review receipts bind that candidate before ``finalize-reviewed-inputs``
can admit it. Then ``prepare-snapshot`` deterministically promotes the admitted
semantic material to READY, derives every launch byte, and publishes an
immutable REVIEW-CANDIDATE. Eight independent snapshot receipts bind that
second candidate. ``finalize`` copies and re-verifies it, adds only the bound
receipts and mechanical finalization records, and creates ``STATIC-LOCK.json``
as the final static byte mutation. There is no one-shot production path.

``self-test`` uses a private SYNTHETIC-TEST-ONLY capability and temporary
directories. It cannot mint a bundle which authenticates as PRODUCTION.
"""

from __future__ import annotations

import argparse
import copy
import ctypes
import errno
import hashlib
import json
import os
import platform
import re
import runpy
import shutil
import ssl
import stat
import subprocess
import sys
import tempfile
import types
from pathlib import Path
from typing import Any, Callable, Iterable

sys.dont_write_bytecode = True
import prepare


RUN = Path(__file__).resolve().parent
SOURCE_DECLARATION = RUN / "static-inputs" / "source-declaration.json"
STATIC_MANIFEST = "STATIC-MANIFEST.sha256"
STATIC_LOCK = "STATIC-LOCK.json"
SNAPSHOT_MANIFEST = "REVIEW-SNAPSHOT.manifest"
SNAPSHOT_DESCRIPTOR = "REVIEW-SNAPSHOT.json"
SOURCE_REVIEW_MANIFEST = "SOURCE-REVIEW.manifest"
SOURCE_REVIEW_DESCRIPTOR = "SOURCE-REVIEW.json"
SOURCE_REVIEW_ALGORITHM = "V5_SOURCE_REVIEW_SNAPSHOT_V1"
SOURCE_REVIEW_TRANSITION_ALGORITHM = "V5_REVIEWED_SOURCE_TRANSITION_V1"
REVIEWED_STATIC_SET_ALGORITHM = "V5_REVIEWED_STATIC_RECORD_SET_V1"
REVIEWER_TOOL_SET_ALGORITHM = "V5_REVIEWER_TOOL_SET_V1"
REVIEWER_RUNTIME_ATTESTATION_ALGORITHM = "V5_REVIEWER_RUNTIME_ATTESTATION_V1"
REVIEW_WORK_PRODUCT_ALGORITHM = "V5_REVIEW_WORK_PRODUCT_V1"
REVIEW_WORK_PRODUCT_NARRATIVE_ALGORITHM = "V5_REVIEW_NARRATIVE_V1"
REVIEW_COVERAGE_SET_ALGORITHM = "V5_REVIEW_COVERAGE_SET_V1"
AUTHENTICATED_REVIEW_EVIDENCE_ALGORITHM = "V5_AUTHENTICATED_REVIEW_EVIDENCE_V1"
SOURCE_REVIEW_PROCEDURE_VERSION = "v5-source-review-v1"
SOURCE_REVIEW_CONTRACT_ROOT = "source-review-contracts"
SOURCE_REVIEW_PROCEDURE_ROOT = "source-review-procedures"
SOURCE_REVIEW_THEOREM_ROOT = "theorem-inputs"
SOURCE_REVIEW_KINDS = (
    ("oracle-review-1.json", "INDEPENDENT_ORACLE"),
    ("oracle-review-2.json", "INDEPENDENT_ORACLE"),
    ("coherence-review.json", "COHERENCE"),
)
SOURCE_REVIEW_CHECK_IDS = {
    "INDEPENDENT_ORACLE": (
        "EXACT-SOURCE-REVIEW-BOUND",
        "REVIEW-CONTRACT-BOUND",
        "ARTIFACT-INVENTORY-CHECKED",
        "EXACT-QUOTATIONS-AND-PAGE-BYTES-VERIFIED",
        "ORACLE-ENTAILMENT-CHECKED",
        "AUTHORITY-PROJECTION-CHECKED",
        "END-OF-REVIEW-REVERIFIED",
    ),
    "COHERENCE": (
        "EXACT-SOURCE-REVIEW-BOUND",
        "REVIEW-CONTRACT-BOUND",
        "ARTIFACT-INVENTORY-CHECKED",
        "CONTROL-AND-DEFECT-COVERAGE-CHECKED",
        "CROSS-FILE-CLOSURE-CHECKED",
        "TRANSFORMATION-CORRECTNESS-CHECKED",
        "END-OF-REVIEW-REVERIFIED",
    ),
}
SOURCE_REVIEW_PROCEDURE_TEXT = {
    "INDEPENDENT_ORACLE": """# V5 independent oracle source review

Use only the verified private copy named by the coordinator as semantic input. Create it with `integrate.py review-source-subject SOURCE_CANDIDATE --private-copy PRIVATE_COPY`. Before reading semantic content, run `integrate.py source-review-custody-check --snapshot SOURCE_CANDIDATE --private-copy PRIVATE_COPY`. Those commands must be run from the separately trusted harness whose complete Python/schema tool set exactly matches the contract's `reviewer_tools` and `reviewer_tool_set_sha256`; run `integrate.py reviewer-runtime-attestation` with that same interpreter to inspect the runtime identity which the receipt builder will bind. The Python interpreter and standard library remain explicit TCB premises. Read the exact contract for this reviewer and check every artifact listed by it.

1. Verify `theorem-inputs/source-declaration.json` and each exact target tree under `theorem-inputs/unsafe-rust/`. Confirm every mode, fixture identity, source path, and BYTE_TREE_V1 digest joins the declaration, fixture manifest, atoms, oracle, controls, and defect rules without substitution.
2. Run `integrate.py verify-source-quotations --private-copy PRIVATE_COPY`. It must fetch every exact versioned official Rust page without redirects, match its frozen full-page SHA-256, validate every cited fragment, and find every exact excerpt within the referenced section. A deliberately fragmentless item-page citation proves only a page-wide, single-semantic-element match on those content-addressed bytes; it makes no subsection claim. Treat any unavailable, ambiguous, or mismatching authority premise as FAIL.
3. For every atom and oracle conclusion, reconstruct the proof from the exact target bytes and cited authoritative propositions. Check preconditions, postconditions, supported configurations, witness reachability, defined-versus-UB distinctions, and all cross-file prerequisites. A hash alone is not semantic evidence.
4. Recompute the agent-visible authority projection and confirm it equals both the reviewed canonical projection and `docs/rust-documentation.json` byte-for-byte, with no evaluator-only material.
5. Record a concise, item-specific proof/rationale for every exact `coverage_items` entry in a work-product JSON object and a narrative report explaining findings and reconstructed proofs; do not collapse any item to a global PASS. Separately author the result JSON with the exact ordered check IDs and evidence required by the contract; a bare assertion of PASS is invalid. Produce no receipt if any required check is incomplete, unresolved, or failed. Otherwise run `integrate.py build-source-review-receipt --snapshot SOURCE_CANDIDATE --private-copy PRIVATE_COPY --review-name REVIEW_NAME --actor-id ACTOR_ID --work-product WORK_PRODUCT.json --result RESULT.json --output RECEIPTS/REVIEW_NAME`. The builder reruns custody, records the actual runtime, fills only deterministic contract/digest fields, validates the reviewer-authored work, reruns custody at the end, and no-replace-publishes one canonical read-only receipt. After all three actors finish, the coordinator must run `integrate.py validate-source-review-receipts --snapshot SOURCE_CANDIDATE --receipts RECEIPTS`.
""",
    "COHERENCE": """# V5 reviewed-source coherence review

Use only the verified private copy named by the coordinator as semantic input. Create it with `integrate.py review-source-subject SOURCE_CANDIDATE --private-copy PRIVATE_COPY`. Before review, run `integrate.py source-review-custody-check --snapshot SOURCE_CANDIDATE --private-copy PRIVATE_COPY`. Those commands must be run from the separately trusted harness whose complete Python/schema tool set exactly matches the contract's `reviewer_tools` and `reviewer_tool_set_sha256`; run `integrate.py reviewer-runtime-attestation` with that same interpreter to inspect the runtime identity which the receipt builder will bind. The Python interpreter and standard library remain explicit TCB premises. Read the exact coherence contract and check every artifact listed by it.

1. Verify the complete artifact inventory, `theorem-inputs/source-declaration.json`, and all target trees under `theorem-inputs/unsafe-rust/`. Confirm every mode-to-source join and BYTE_TREE_V1 identity is exact.
2. Check all atom prerequisites and inverse authority consumers, every allowlist URL, fixture surface and supported-set declaration, control coverage, defect-rule coverage, and mode/fixture/source cross-reference. Reject missing, stale, duplicated, or contradictory records.
3. Check the mechanical DRAFT-to-SOURCE-REVIEW-CANDIDATE transformation: semantic text is unchanged except exact lifecycle fields/markers and self-describing source bindings; no candidate file claims completed review or a not-yet-derived report-material digest.
4. Confirm `docs/rust-documentation.json` is byte-identical to the canonical reviewed projection and that the review subject contains no unbound target, authority, procedure, or receipt-schema input.
5. Record a concise, item-specific rationale for every exact `coverage_items` entry in a work-product JSON object and a narrative report explaining every finding; do not collapse any item to a path-level or global PASS. Separately author the result JSON with the exact ordered check IDs and evidence required by the contract; a bare assertion of PASS is invalid. Produce no receipt if any required check is incomplete, unresolved, or failed. Otherwise run `integrate.py build-source-review-receipt --snapshot SOURCE_CANDIDATE --private-copy PRIVATE_COPY --review-name coherence-review.json --actor-id ACTOR_ID --work-product WORK_PRODUCT.json --result RESULT.json --output RECEIPTS/coherence-review.json`. The builder reruns custody, records the actual runtime, fills only deterministic contract/digest fields, validates the reviewer-authored work, reruns custody at the end, and no-replace-publishes one canonical read-only receipt. After all three actors finish, the coordinator must run `integrate.py validate-source-review-receipts --snapshot SOURCE_CANDIDATE --receipts RECEIPTS`.
""",
}
EXACT_QUOTATION_EVIDENCE_ALGORITHM = "V5_EXACT_QUOTATION_EVIDENCE_V1"
EXACT_QUOTATION_EVIDENCE_SHA256 = (
    "a3aff9b35d747b8dc12c90d8484f37d531447122ec186509ca62baa5e360bcaa"
)
REPORT_MATERIAL_SET_ALGORITHM = "V5_MODE_REPORT_MATERIAL_SET_V1"
SOURCE_REVIEW_CANDIDATE_STATUS = "SOURCE-REVIEW-CANDIDATE"
REVIEWED_FIXTURE_STATUS = SOURCE_REVIEW_CANDIDATE_STATUS
REVIEWED_DERIVATION_SENTINEL = "DERIVE_DURING_SNAPSHOT_BUILD"
REVIEWED_STATIC_DERIVED_BASE = "DERIVED-BY-TRUSTED-SOURCE-REVIEW-BUILDER"
REVIEWED_STATIC_CANDIDATE_BASE = "reviewed-static"
REVIEWED_STATIC_BUNDLE_BASE = "static/integration/reviewed-static-input"
EXTERNAL_COMMITMENT_STATUS = "EXTERNAL-TRUST-COMMITMENT"
RECOVERY_CUSTODY_ACKNOWLEDGEMENT = (
    "UNINTERRUPTED_TRUSTED_COORDINATOR_CUSTODY_SINCE_FINALIZATION"
)
RUNTIME_ROOT = "runtime"
RUNTIME_STATE = "runtime/state"
MANIFEST_ALGORITHM = "V5_DOMAIN_FRAMED_TREE_V1"
PATH_DOMAIN = "PORTABLE_ASCII_RELATIVE_PATH_V1"
BUNDLE_KINDS = ("PRODUCTION", "SYNTHETIC-TEST-ONLY")
PHASES = (
    "SNAPSHOT_BUILD",
    "SNAPSHOT_REVIEW",
    "FINALIZE_STATIC",
    "RUNTIME_COLLECTION",
    "POSTRUN_AGGREGATE",
)
ROLE_NAMES = (
    "report",
    "scorer",
    "consistency",
    "adjudicator",
    "materiality-reviewer",
    "materiality-adjudicator",
)
STRUCTURAL_HOOKS = (
    "H-BUILD-WHOLE-FILE-MANIFEST",
    "H-CREATE-LOCK-LAST",
)
HOOK_PHASES = {
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
EXTERNAL_REVIEW_HOOKS = {
    "H-VALIDATE-CROSS-REFERENCE-CLOSURE",
    "H-VALIDATE-HIDDEN-FIXTURE-MANIFESTS",
    "H-VALIDATE-ORACLE-COVERAGE",
    "H-VALIDATE-INDEPENDENT-SIGNOFFS",
    "H-BUILD-VALIDATE-REPORT-AUTHORITY-PROJECTIONS",
    "H-VALIDATE-PROMPT-RENDERINGS",
    "H-GENERATE-VERIFY-RANDOMIZATION",
    "H-VALIDATE-AGGREGATION-RULE-INVENTORY",
}
HOOK_IMPLEMENTATION = {
    hook_id: (
        "INDEPENDENT_RECEIPT_REQUIRED"
        if phase == "SNAPSHOT_REVIEW"
        else "RUNTIME_RECEIPT_REQUIRED"
        if phase in {"RUNTIME_COLLECTION", "POSTRUN_AGGREGATE"}
        else "DIRECTLY_REVALIDATED"
    )
    for hook_id, phase in HOOK_PHASES.items()
}
HEX64 = re.compile(r"^[0-9a-f]{64}$")
ACTOR_ID = re.compile(r"^[a-z0-9][a-z0-9._-]{15,127}$")
OPAQUE_WORKSPACE_LEAF = re.compile(r"^[0-9a-f]{64}$")
_SYNTHETIC_CAPABILITY = object()
_FINALIZATION_PRECOMMIT_CAPABILITY = object()
_RECOVERY_PRECOMMIT_CAPABILITY = object()
BASELINE_CONTENT_FORBIDDEN_TOKENS = frozenset({"no_skill", "no-skill"})
PACKAGE_CROSS_CONDITION_FORBIDDEN_TOKENS = frozenset(
    {
        "no_skill",
        "no-skill",
        "blind-map",
        "condition_label",
        "target_label",
        "launch-schedule",
        "presentation-orders",
        "scoring-schedule",
        "consistency-schedule",
    }
)
SNAPSHOT_REVIEW_PROCEDURE_VERSION = "v5-snapshot-review-v1"
SNAPSHOT_REVIEW_PROCEDURE_PATH = (
    "static/integration/snapshot-review-procedure.md"
)
SNAPSHOT_REVIEW_RECEIPT_SCHEMA_PATH = "schemas/integration-receipt.schema.json"
SNAPSHOT_REVIEW_CHECK_IDS = (
    "EXACT-SNAPSHOT-BOUND",
    "REVIEW-CONTRACT-BOUND",
    "ARTIFACT-INVENTORY-CHECKED",
    "HOOK-SEMANTICS-CHECKED",
    "END-OF-REVIEW-REVERIFIED",
)
SNAPSHOT_REVIEW_ACCEPTANCE_REQUIREMENTS = {
    "H-VALIDATE-CROSS-REFERENCE-CLOSURE": (
        "Verify exact stable IDs, schema/status fields, file inventories, and every forward/inverse cross-file join; reject any missing, extra, stale, duplicated, or contradictory record.",
    ),
    "H-VALIDATE-HIDDEN-FIXTURE-MANIFESTS": (
        "For every mode, verify the trusted target source-tree identity, supported configuration set, safe/public surface inventory, control joins, all fifteen exact report-material bindings, and the complete reused-P lineage.",
    ),
    "H-VALIDATE-ORACLE-COVERAGE": (
        "Verify every atom, prerequisite edge, inverse authority consumer, exact quotation locator, allowlist URL, oracle conclusion, control, and defect-rule obligation is complete and entailed by the exact reviewed theorem inputs.",
    ),
    "H-VALIDATE-INDEPENDENT-SIGNOFFS": (
        "Verify the exact three source-review receipts and contracts, pairwise-distinct claimed reviewer identities, procedure/evidence coverage, immutable subject digests, and end-of-review custody reverification; treat out-of-band identity authentication as an explicit coordinator TCB premise rather than inferring it from bundle bytes.",
    ),
    "H-BUILD-VALIDATE-REPORT-AUTHORITY-PROJECTIONS": (
        "Rebuild the exact allowed report-agent authority projection; verify every mounted copy is byte-identical and contains neither evaluator-only material nor an unapproved authority/source path.",
    ),
    "H-VALIDATE-PROMPT-RENDERINGS": (
        "Rebuild and compare all 120 report prompts, input plans, launch records, exact mounts, role manifests, envelope specs, and all 43 evaluator contracts/prompts; verify cross-condition differential isolation and absence of unresolved markers.",
    ),
    "H-GENERATE-VERIFY-RANDOMIZATION": (
        "Recompute every seed-derived condition, target, blind, launch, presentation, scoring, and consistency map; verify balance, blinding, reviewer assignment separation, and exact randomization commitments.",
    ),
    "H-VALIDATE-AGGREGATION-RULE-INVENTORY": (
        "Verify complete fail-closed aggregation, comparison, materiality, gate, and root topology, including exact predicates, thresholds, prerequisites, decision domains, and every required output/input join.",
    ),
}


class IntegrationError(ValueError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
            allow_nan=False,
        )
        + "\n"
    ).encode("utf-8")


def pretty_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, indent=2, ensure_ascii=False, allow_nan=False)
        + "\n"
    ).encode("utf-8")


def require_actor_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or ACTOR_ID.fullmatch(value) is None:
        raise IntegrationError(
            f"{label} must be 16-128 lowercase ASCII safe-ID characters"
        )
    return value


def current_reviewer_runtime_attestation() -> dict[str, str | int]:
    return {
        "schema_version": 1,
        "algorithm": REVIEWER_RUNTIME_ATTESTATION_ALGORITHM,
        "python_implementation": platform.python_implementation(),
        "python_version": platform.python_version(),
        "python_cache_tag": sys.implementation.cache_tag or "NONE",
        "openssl_version": ssl.OPENSSL_VERSION,
        "platform_system": platform.system(),
        "platform_release": platform.release(),
        "platform_machine": platform.machine(),
    }


def validate_reviewer_runtime_attestation(value: Any) -> dict[str, Any]:
    runtime = exact_object(
        value,
        {
            "schema_version",
            "algorithm",
            "python_implementation",
            "python_version",
            "python_cache_tag",
            "openssl_version",
            "platform_system",
            "platform_release",
            "platform_machine",
        },
        "reviewer runtime attestation",
    )
    if (
        runtime["schema_version"] != 1
        or runtime["algorithm"] != REVIEWER_RUNTIME_ATTESTATION_ALGORITHM
        or any(
            not isinstance(runtime[field], str)
            or not runtime[field]
            or not runtime[field].isascii()
            or any(ord(character) < 0x20 for character in runtime[field])
            for field in runtime
            if field not in {"schema_version", "algorithm"}
        )
    ):
        raise IntegrationError("reviewer runtime attestation is not exact ASCII metadata")
    return runtime


def review_coverage_set_sha256(items: list[dict[str, str]]) -> str:
    return sha256(
        REVIEW_COVERAGE_SET_ALGORITHM.encode("ascii")
        + b"\0"
        + canonical_json_bytes(items)
    )


def review_work_product_sha256(value: dict[str, Any]) -> str:
    return sha256(
        REVIEW_WORK_PRODUCT_ALGORITHM.encode("ascii")
        + b"\0"
        + canonical_json_bytes(value)
    )


def validate_review_work_product(
    value: Any,
    *,
    expected_coverage_items: list[dict[str, str]],
) -> tuple[dict[str, Any], str]:
    work = exact_object(
        value,
        {"algorithm", "narrative", "narrative_sha256", "coverage"},
        "review work product",
    )
    narrative = work["narrative"]
    if (
        work["algorithm"] != REVIEW_WORK_PRODUCT_ALGORITHM
        or not isinstance(narrative, str)
        or len(narrative.strip()) < 100
    ):
        raise IntegrationError("review work product narrative is not substantive")
    expected_narrative_sha256 = sha256(
        REVIEW_WORK_PRODUCT_NARRATIVE_ALGORITHM.encode("ascii")
        + b"\0"
        + narrative.encode("utf-8")
    )
    if work["narrative_sha256"] != expected_narrative_sha256:
        raise IntegrationError("review work product narrative digest is wrong")
    coverage = work["coverage"]
    if not isinstance(coverage, list) or len(coverage) != len(expected_coverage_items):
        raise IntegrationError("review work product coverage count is not exact")
    observed_items: list[dict[str, str]] = []
    for index, raw in enumerate(coverage):
        item = exact_object(
            raw,
            {"id", "subject", "decision", "rationale"},
            f"review work product coverage {index}",
        )
        observed_items.append({"id": item["id"], "subject": item["subject"]})
        if (
            item["decision"] != "PASS"
            or not isinstance(item["rationale"], str)
            or len(item["rationale"].strip()) < 40
            or item["id"] not in item["rationale"]
        ):
            raise IntegrationError(
                f"review work product rationale is not item-specific: {item['id']}"
            )
    if observed_items != expected_coverage_items:
        raise IntegrationError("review work product coverage IDs/subjects are not exact")
    return work, review_work_product_sha256(work)


def synthetic_review_work_product(
    coverage_items: list[dict[str, str]], *, label: str
) -> dict[str, Any]:
    """Build a private self-test work product; never used by a public command."""

    narrative = (
        f"Synthetic self-test work product for {label}. This record exercises exact "
        "coverage inventory, canonical serialization, digest binding, and rejection "
        "paths only; it is not an independent semantic review and cannot authorize "
        "a production artifact."
    )
    return {
        "algorithm": REVIEW_WORK_PRODUCT_ALGORITHM,
        "narrative": narrative,
        "narrative_sha256": sha256(
            REVIEW_WORK_PRODUCT_NARRATIVE_ALGORITHM.encode("ascii")
            + b"\0"
            + narrative.encode("utf-8")
        ),
        "coverage": [
            {
                **item,
                "decision": "PASS",
                "rationale": (
                    f"{item['id']}: synthetic self-test exercised the exact bound "
                    "coverage identity and subject without claiming human review."
                ),
            }
            for item in coverage_items
        ],
    }


def reject_nonfinite(value: str) -> Any:
    raise IntegrationError(f"non-finite JSON number is forbidden: {value}")


def unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise IntegrationError(f"duplicate JSON object key is forbidden: {key!r}")
        result[key] = value
    return result


def parse_json_bytes(data: bytes, label: str) -> Any:
    try:
        text = data.decode("utf-8", errors="strict")
        return json.loads(
            text,
            object_pairs_hook=unique_object,
            parse_constant=reject_nonfinite,
        )
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise IntegrationError(f"cannot parse strict JSON {label}: {error}") from error


def read_json(path: Path) -> Any:
    try:
        return parse_json_bytes(path.read_bytes(), str(path))
    except OSError as error:
        raise IntegrationError(f"cannot read JSON {path}: {error}") from error


def capture_regular_file_bytes(
    path: Path, label: str, *, require_read_only: bool
) -> bytes:
    """Capture one regular file through one no-follow descriptor."""

    required_flags = ("O_NOFOLLOW", "O_CLOEXEC", "O_NONBLOCK")
    if any(not hasattr(os, name) for name in required_flags):
        raise IntegrationError(
            f"{label} cannot be read without no-follow, close-on-exec, and nonblocking opens"
        )
    flags = os.O_RDONLY
    for name in required_flags:
        flags |= getattr(os, name)
    descriptor: int | None = None
    try:
        descriptor = os.open(path, flags)
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise IntegrationError(f"{label} must be a real regular file")
        if require_read_only and before.st_mode & 0o222:
            raise IntegrationError(f"{label} must be read-only")
        chunks: list[bytes] = []
        while True:
            chunk = os.read(descriptor, 1024 * 1024)
            if not chunk:
                break
            chunks.append(chunk)
        data = b"".join(chunks)
        after = os.fstat(descriptor)
        before_identity = (
            before.st_dev,
            before.st_ino,
            before.st_mode,
            before.st_nlink,
            before.st_uid,
            before.st_gid,
            before.st_size,
            before.st_mtime_ns,
            before.st_ctime_ns,
        )
        after_identity = (
            after.st_dev,
            after.st_ino,
            after.st_mode,
            after.st_nlink,
            after.st_uid,
            after.st_gid,
            after.st_size,
            after.st_mtime_ns,
            after.st_ctime_ns,
        )
        if before_identity != after_identity:
            raise IntegrationError(f"{label} identity or mode changed while it was read")
        if not stat.S_ISREG(after.st_mode) or (
            require_read_only and after.st_mode & 0o222
        ):
            raise IntegrationError(f"{label} lost its required regular-file identity")
    except OSError as error:
        raise IntegrationError(f"cannot securely open/read {label}: {error}") from error
    finally:
        if descriptor is not None:
            os.close(descriptor)
    return data


def read_canonical_read_only_json(path: Path, label: str) -> tuple[Any, bytes]:
    """Capture one production receipt through one immutable file descriptor."""

    data = capture_regular_file_bytes(path, label, require_read_only=True)
    value = parse_json_bytes(data, label)
    if data != canonical_json_bytes(value):
        raise IntegrationError(f"{label} must use exact canonical JSON bytes")
    return value, data


def capture_review_receipt_json(
    path: Path,
    label: str,
    *,
    synthetic_capability: object | None,
) -> tuple[Any, bytes]:
    """Capture receipt bytes once; production uses the descriptor-bound predicate."""

    if synthetic_capability is _SYNTHETIC_CAPABILITY:
        try:
            data = path.read_bytes()
        except OSError as error:
            raise IntegrationError(f"cannot read {label}: {error}") from error
        return parse_json_bytes(data, label), data
    return read_canonical_read_only_json(path, label)


def exact_object(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        raise IntegrationError(f"{label} keys must be exactly {sorted(keys)}")
    return value


def digest(value: Any, label: str) -> str:
    if not isinstance(value, str) or not HEX64.fullmatch(value):
        raise IntegrationError(f"{label} must be a lowercase SHA-256 digest")
    return value


def relative(value: Any, label: str) -> str:
    if not isinstance(value, str):
        raise IntegrationError(f"{label} must be a path string")
    try:
        prepare.portable_relative_path(value, label)
    except ValueError as error:
        raise IntegrationError(str(error)) from error
    return value


def absolute_normalized(path: Path, label: str) -> Path:
    if not path.is_absolute() or path.resolve() != path:
        raise IntegrationError(f"{label} must be an absolute normalized path")
    return path


def require_neutral_workspace_base(path: Path, forbidden_terms: Iterable[str]) -> Path:
    """Validate the coordinator-only absolute root behind fixed agent aliases."""

    path = absolute_normalized(path, "workspace base")
    lowered = str(path).lower()
    matches = sorted({term for term in forbidden_terms if term.lower() in lowered})
    if matches:
        raise IntegrationError(
            "workspace base is not a neutral opaque absolute path; "
            f"matched forbidden terms: {matches}"
        )
    if not OPAQUE_WORKSPACE_LEAF.fullmatch(path.name):
        raise IntegrationError(
            "workspace base leaf must be exactly 64 lowercase hexadecimal characters"
        )
    return path


def paths_overlap(first: Path, second: Path) -> bool:
    return first == second or first in second.parents or second in first.parents


def require_disjoint_review_subjects(
    snapshot: Path, private_copy: Path, label: str
) -> tuple[Path, Path]:
    """Resolve and reject reflexive or nested source/private review subjects."""

    source = snapshot.resolve()
    private = private_copy.resolve()
    if paths_overlap(source, private):
        raise IntegrationError(f"{label} source and private copy must be disjoint")
    return source, private


def neutral_self_test_parent(forbidden_terms: Iterable[str]) -> Path:
    """Choose a real neutral parent without trusting a treatment-leaking TMPDIR."""

    terms = tuple(forbidden_terms)
    candidates = (Path("/tmp"), Path(tempfile.gettempdir()))
    examined: set[Path] = set()
    for candidate in candidates:
        try:
            resolved = candidate.resolve(strict=True)
        except OSError:
            continue
        if resolved in examined or not resolved.is_dir():
            continue
        examined.add(resolved)
        try:
            lowered = str(resolved).lower()
            if any(term.lower() in lowered for term in terms):
                continue
        except (IntegrationError, OSError):
            continue
        return resolved
    raise IntegrationError(
        "synthetic integration self-test has no neutral temporary parent; "
        "ambient TMPDIR is not permitted to weaken path-neutrality validation"
    )


def write_exclusive(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        with path.open("xb") as file:
            file.write(data)
            file.flush()
            os.fsync(file.fileno())
        fsync_directory(path.parent)
    except FileExistsError as error:
        raise IntegrationError(f"refusing to replace existing static file: {path}") from error


def write_json(path: Path, value: Any) -> None:
    write_exclusive(path, pretty_json_bytes(value))


def canonical_new_file_destination(path: Path, label: str) -> Path:
    """Resolve a new file's parent without following its terminal component."""

    absolute = Path(os.path.abspath(path))
    absolute.parent.mkdir(parents=True, exist_ok=True)
    parent = absolute.parent.resolve(strict=True)
    destination = parent / absolute.name
    if os.path.lexists(destination):
        raise IntegrationError(f"{label} already exists: {destination}")
    return destination


def external_commitment_destination(
    bundle_root: Path, path: Path, label: str
) -> Path:
    """Require a missing destination whose resolved location is outside a bundle."""

    root = bundle_root.resolve(strict=False)
    absolute = Path(os.path.abspath(path))
    prospective = absolute.parent.resolve(strict=False) / absolute.name
    if paths_overlap(prospective, root):
        raise IntegrationError(f"{label} must be separately custodied outside the bundle")
    destination = canonical_new_file_destination(absolute, label)
    if paths_overlap(destination, root):
        raise IntegrationError(f"{label} must be separately custodied outside the bundle")
    return destination


def publish_read_only_canonical_json(
    path: Path, value: dict[str, Any], *, label: str
) -> None:
    """Durably stage and no-replace-publish one canonical read-only JSON file."""

    destination = canonical_new_file_destination(path, label)
    data = canonical_json_bytes(value)
    descriptor, stage_text = tempfile.mkstemp(
        prefix=f".{destination.name}.v5-json-stage-",
        dir=destination.parent,
    )
    stage = Path(stage_text)
    try:
        with os.fdopen(descriptor, "wb") as file:
            descriptor = -1
            file.write(data)
            file.flush()
            os.fsync(file.fileno())
            os.fchmod(file.fileno(), 0o444)
            os.fsync(file.fileno())
        publish_no_replace(stage, destination)
        if (
            destination.read_bytes() != data
            or stat.S_IMODE(destination.stat(follow_symlinks=False).st_mode) != 0o444
        ):
            raise IntegrationError(
                f"published {label} is not the exact read-only staged file"
            )
    except Exception:
        if descriptor >= 0:
            os.close(descriptor)
        if os.path.lexists(stage):
            stage.unlink()
            fsync_directory(stage.parent)
        raise


def _publish_external_commitment_file(path: Path, value: dict[str, Any]) -> None:
    """Durably publish a separately custodied external commitment."""

    publish_read_only_canonical_json(
        path, value, label="external commitment output"
    )


def fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def reject_unsupported_tree(root: Path, label: str) -> None:
    if root.is_symlink() or not root.is_dir():
        raise IntegrationError(f"{label} must be a real directory: {root}")
    for item in root.rglob("*"):
        if item.is_symlink() or not (item.is_dir() or item.is_file()):
            raise IntegrationError(f"{label} contains a symlink or special entry: {item}")


def copy_tree(source: Path, destination: Path) -> None:
    reject_unsupported_tree(source, "copy source")
    if destination.exists():
        raise IntegrationError(f"copy destination already exists: {destination}")
    shutil.copytree(source, destination, symlinks=False)


def strict_equal(first: Any, second: Any) -> bool:
    """JSON equality which does not conflate booleans and integers."""

    return type(first) is type(second) and first == second


def validate_json_schema(
    instance: Any,
    schema: Any,
    *,
    label: str,
    root_schema: dict[str, Any] | None = None,
) -> None:
    """Validate the closed JSON-Schema 2020-12 subset used by integration.

    The repository intentionally has no runtime package dependency. This
    validator therefore implements—and rejects anything outside—the small,
    auditable subset used by the integration schemas. It is not presented as a
    general JSON-Schema implementation.
    """

    if not isinstance(schema, dict):
        raise IntegrationError(f"{label}: schema node must be an object")
    if root_schema is None:
        root_schema = schema
    allowed = {
        "$schema",
        "$id",
        "$comment",
        "$defs",
        "$ref",
        "type",
        "const",
        "enum",
        "required",
        "properties",
        "additionalProperties",
        "items",
        "minItems",
        "maxItems",
        "uniqueItems",
        "minProperties",
        "maxProperties",
        "minLength",
        "pattern",
        "minimum",
        "oneOf",
        "allOf",
        "if",
        "then",
        "else",
        "not",
    }
    unsupported = set(schema) - allowed
    if unsupported:
        raise IntegrationError(
            f"{label}: unsupported JSON-Schema keywords {sorted(unsupported)}"
        )
    if "$ref" in schema:
        reference = schema["$ref"]
        if not isinstance(reference, str) or not reference.startswith("#/$defs/"):
            raise IntegrationError(f"{label}: only local $defs references are supported")
        name = reference.removeprefix("#/$defs/")
        definitions = root_schema.get("$defs")
        if not isinstance(definitions, dict) or name not in definitions:
            raise IntegrationError(f"{label}: unresolved schema reference {reference!r}")
        validate_json_schema(
            instance,
            definitions[name],
            label=label,
            root_schema=root_schema,
        )
        return
    for index, subschema in enumerate(schema.get("allOf", [])):
        validate_json_schema(
            instance,
            subschema,
            label=f"{label}.allOf[{index}]",
            root_schema=root_schema,
        )
    if "if" in schema:
        try:
            validate_json_schema(
                instance,
                schema["if"],
                label=f"{label}.if",
                root_schema=root_schema,
            )
        except IntegrationError:
            if "else" in schema:
                validate_json_schema(
                    instance,
                    schema["else"],
                    label=f"{label}.else",
                    root_schema=root_schema,
                )
        else:
            if "then" in schema:
                validate_json_schema(
                    instance,
                    schema["then"],
                    label=f"{label}.then",
                    root_schema=root_schema,
                )
    if "not" in schema:
        try:
            validate_json_schema(
                instance,
                schema["not"],
                label=f"{label}.not",
                root_schema=root_schema,
            )
        except IntegrationError:
            pass
        else:
            raise IntegrationError(f"{label}: value matched forbidden schema")
    if "oneOf" in schema:
        successes = 0
        for subschema in schema["oneOf"]:
            try:
                validate_json_schema(
                    instance,
                    subschema,
                    label=label,
                    root_schema=root_schema,
                )
            except IntegrationError:
                pass
            else:
                successes += 1
        if successes != 1:
            raise IntegrationError(f"{label}: oneOf matched {successes} branches")
    if "const" in schema and not strict_equal(instance, schema["const"]):
        raise IntegrationError(f"{label}: value does not equal schema const")
    if "enum" in schema and not any(strict_equal(instance, item) for item in schema["enum"]):
        raise IntegrationError(f"{label}: value is not in schema enum")
    expected_type = schema.get("type")
    predicates = {
        "object": lambda value: isinstance(value, dict),
        "array": lambda value: isinstance(value, list),
        "string": lambda value: isinstance(value, str),
        "integer": lambda value: type(value) is int,
        "number": lambda value: type(value) in {int, float},
        "boolean": lambda value: type(value) is bool,
        "null": lambda value: value is None,
    }
    if expected_type is not None:
        if expected_type not in predicates or not predicates[expected_type](instance):
            raise IntegrationError(f"{label}: value is not JSON type {expected_type!r}")
    if isinstance(instance, dict):
        required = schema.get("required", [])
        if not isinstance(required, list) or any(not isinstance(key, str) for key in required):
            raise IntegrationError(f"{label}: schema required must be a string array")
        missing = set(required) - set(instance)
        if missing:
            raise IntegrationError(f"{label}: missing required keys {sorted(missing)}")
        properties = schema.get("properties", {})
        if not isinstance(properties, dict):
            raise IntegrationError(f"{label}: schema properties must be an object")
        extras = set(instance) - set(properties)
        additional = schema.get("additionalProperties", True)
        if extras and additional is False:
            raise IntegrationError(f"{label}: unexpected keys {sorted(extras)}")
        for key, value in instance.items():
            if key in properties:
                validate_json_schema(
                    value,
                    properties[key],
                    label=f"{label}.{key}",
                    root_schema=root_schema,
                )
            elif isinstance(additional, dict):
                validate_json_schema(
                    value,
                    additional,
                    label=f"{label}.{key}",
                    root_schema=root_schema,
                )
        for keyword, comparison in (
            ("minProperties", lambda actual, expected: actual >= expected),
            ("maxProperties", lambda actual, expected: actual <= expected),
        ):
            if keyword in schema and not comparison(len(instance), schema[keyword]):
                raise IntegrationError(f"{label}: object violates {keyword}")
    if isinstance(instance, list):
        for keyword, comparison in (
            ("minItems", lambda actual, expected: actual >= expected),
            ("maxItems", lambda actual, expected: actual <= expected),
        ):
            if keyword in schema and not comparison(len(instance), schema[keyword]):
                raise IntegrationError(f"{label}: array violates {keyword}")
        if schema.get("uniqueItems") is True:
            encoded = [canonical_json_bytes(item) for item in instance]
            if len(set(encoded)) != len(encoded):
                raise IntegrationError(f"{label}: array items are not unique")
        if "items" in schema:
            for index, item in enumerate(instance):
                validate_json_schema(
                    item,
                    schema["items"],
                    label=f"{label}[{index}]",
                    root_schema=root_schema,
                )
    if isinstance(instance, str):
        if "minLength" in schema and len(instance) < schema["minLength"]:
            raise IntegrationError(f"{label}: string is shorter than minLength")
        if "pattern" in schema and re.search(schema["pattern"], instance) is None:
            raise IntegrationError(f"{label}: string does not match schema pattern")
    if type(instance) in {int, float} and "minimum" in schema and instance < schema["minimum"]:
        raise IntegrationError(f"{label}: number is below schema minimum")


def validate_schema_file(instance: Any, schema_path: Path, label: str) -> None:
    schema = read_json(schema_path)
    if schema.get("$schema") != "https://json-schema.org/draft/2020-12/schema":
        raise IntegrationError(f"{schema_path}: not a declared JSON Schema 2020-12 document")
    validate_json_schema(instance, schema, label=label)


def framed_u64(value: int) -> bytes:
    if value < 0 or value >= 1 << 64:
        raise IntegrationError("manifest integer is outside unsigned 64-bit range")
    return value.to_bytes(8, "big")


def framed_record(
    *,
    domain: bytes,
    kind: bytes,
    path_bytes: bytes,
    size: int,
    content_sha256: bytes,
    mode: int | None,
) -> bytes:
    """Encode one injective domain-separated tree record."""

    if len(kind) != 1 or len(content_sha256) != 32:
        raise IntegrationError("invalid framed-manifest record fields")
    mode_bytes = b"" if mode is None else mode.to_bytes(4, "big")
    return (
        domain
        + b"\0RECORD\0"
        + kind
        + framed_u64(len(path_bytes))
        + path_bytes
        + framed_u64(size)
        + framed_u64(len(mode_bytes))
        + mode_bytes
        + content_sha256
    )


def tree_manifest_bytes(
    root: Path,
    *,
    domain: bytes,
    excluded: Callable[[Path], bool],
    include_mode: bool,
) -> bytes:
    """Return an injective file-and-directory inventory for an exact tree."""

    reject_unsupported_tree(root, "manifest tree")
    records: list[tuple[bytes, bytes]] = []
    for path in root.rglob("*"):
        relative_path = path.relative_to(root)
        if excluded(relative_path):
            continue
        path_text = relative_path.as_posix()
        path_bytes = prepare.portable_relative_path(path_text, "manifest entry")
        metadata = path.stat(follow_symlinks=False)
        mode = stat.S_IMODE(metadata.st_mode) if include_mode else None
        if path.is_dir():
            record = framed_record(
                domain=domain,
                kind=b"D",
                path_bytes=path_bytes,
                size=0,
                content_sha256=b"\0" * 32,
                mode=mode,
            )
        elif path.is_file():
            data = path.read_bytes()
            record = framed_record(
                domain=domain,
                kind=b"F",
                path_bytes=path_bytes,
                size=len(data),
                content_sha256=bytes.fromhex(sha256(data)),
                mode=mode,
            )
        else:
            raise IntegrationError(f"unsupported manifest entry: {path_text}")
        records.append((path_bytes, record))
    records.sort(key=lambda item: item[0])
    return domain + b"\0TREE\0" + framed_u64(len(records)) + b"".join(
        record for _, record in records
    )


def parse_tree_manifest_records(
    payload: bytes,
    *,
    domain: bytes,
    include_mode: bool,
    label: str,
) -> dict[str, dict[str, Any]]:
    """Parse one exact framed tree without consulting any filesystem path."""

    position = 0

    def take(length: int, field: str) -> bytes:
        nonlocal position
        if length < 0 or position + length > len(payload):
            raise IntegrationError(f"{label}: truncated {field}")
        result = payload[position : position + length]
        position += length
        return result

    def take_u64(field: str) -> int:
        return int.from_bytes(take(8, field), "big")

    prefix = domain + b"\0TREE\0"
    if take(len(prefix), "tree prefix") != prefix:
        raise IntegrationError(f"{label}: invalid tree domain or prefix")
    count = take_u64("record count")
    records: dict[str, dict[str, Any]] = {}
    previous_path: bytes | None = None
    record_prefix = domain + b"\0RECORD\0"
    for index in range(count):
        if take(len(record_prefix), f"record {index} prefix") != record_prefix:
            raise IntegrationError(f"{label}: invalid record {index} domain or prefix")
        kind = take(1, f"record {index} kind")
        if kind not in {b"D", b"F"}:
            raise IntegrationError(f"{label}: invalid record {index} kind")
        path_bytes = take(
            take_u64(f"record {index} path length"), f"record {index} path"
        )
        try:
            path_text = path_bytes.decode("utf-8", errors="strict")
        except UnicodeDecodeError as error:
            raise IntegrationError(f"{label}: record {index} path is not UTF-8") from error
        try:
            canonical_path = prepare.portable_relative_path(
                path_text, f"{label} record {index} path"
            )
        except ValueError as error:
            raise IntegrationError(str(error)) from error
        if canonical_path != path_bytes:
            raise IntegrationError(f"{label}: record {index} path is not canonical")
        if previous_path is not None and path_bytes <= previous_path:
            raise IntegrationError(f"{label}: record paths are not strictly ordered")
        previous_path = path_bytes
        size = take_u64(f"record {index} size")
        mode_length = take_u64(f"record {index} mode length")
        expected_mode_length = 4 if include_mode else 0
        if mode_length != expected_mode_length:
            raise IntegrationError(f"{label}: record {index} mode framing is invalid")
        mode_bytes = take(mode_length, f"record {index} mode")
        mode = int.from_bytes(mode_bytes, "big") if include_mode else None
        content_sha256 = take(32, f"record {index} content digest").hex()
        if kind == b"D" and (size != 0 or content_sha256 != "0" * 64):
            raise IntegrationError(f"{label}: directory record {index} has file content")
        records[path_text] = {
            "kind": kind.decode("ascii"),
            "size": size,
            "mode": mode,
            "content_sha256": content_sha256,
        }
    if position != len(payload):
        raise IntegrationError(f"{label}: trailing bytes follow the framed record set")
    return records


def publish_no_replace(stage: Path, output: Path) -> None:
    """Atomically publish one filesystem entry without replacing an extant path."""

    if stage.parent != output.parent:
        raise IntegrationError("no-replace publication requires a same-directory stage")
    libc = ctypes.CDLL(None, use_errno=True)
    renameat2 = getattr(libc, "renameat2", None)
    if renameat2 is None:
        raise IntegrationError("production publication requires renameat2(RENAME_NOREPLACE)")
    renameat2.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    renameat2.restype = ctypes.c_int
    at_fdcwd = -100
    rename_noreplace = 1
    result = renameat2(
        at_fdcwd,
        os.fsencode(stage),
        at_fdcwd,
        os.fsencode(output),
        rename_noreplace,
    )
    if result != 0:
        error = ctypes.get_errno()
        if error == errno.EEXIST:
            raise IntegrationError(f"refusing to replace existing output: {output}")
        raise IntegrationError(f"renameat2 publication failed for {output}: {os.strerror(error)}")
    fsync_directory(output.parent)


def validate_source_declaration(value: Any, *, production: bool) -> dict[str, Any]:
    declaration = exact_object(
        value,
        {
            "schema_version",
            "status",
            "byte_tree_algorithm",
            "source_paths_relative_to",
            "packages",
            "targets",
            "agent_visible_aliases",
        },
        "source declaration",
    )
    if (
        declaration["schema_version"] != 1
        or declaration["status"] != "DRAFT-SOURCE-SELECTION"
        or declaration["byte_tree_algorithm"] != prepare.BYTE_TREE_ALGORITHM
        or declaration["source_paths_relative_to"] != "unsafe-rust-root"
    ):
        raise IntegrationError("source declaration version/status/algorithm drifted")
    aliases = declaration["agent_visible_aliases"]
    if aliases != {
        "input": "input",
        "output": "output",
        "target": "target",
        "package": "package",
        "authority": "docs/rust-documentation.json",
    }:
        raise IntegrationError("agent-visible alias declaration drifted")
    packages = declaration["packages"]
    if not isinstance(packages, dict) or set(packages) != set(prepare.CONDITIONS):
        raise IntegrationError("source declaration package roles are not exact")
    if packages["no_skill"] is not None:
        raise IntegrationError("no_skill source must be literal null")
    for role in ("v5", "v4"):
        package = exact_object(
            packages[role],
            {"source_path", "skill_path", "directory_name_is_byte_tree_sha256"},
            f"{role} source",
        )
        relative(package["source_path"], f"{role} source_path")
        relative(package["skill_path"], f"{role} skill_path")
        if package["directory_name_is_byte_tree_sha256"] is not True:
            raise IntegrationError(f"{role} package directory-name identity must be required")
    targets = declaration["targets"]
    if not isinstance(targets, list) or len(targets) != len(prepare.MODES):
        raise IntegrationError("source declaration must contain exactly eight targets")
    by_mode: dict[str, dict[str, Any]] = {}
    for raw in targets:
        target = exact_object(
            raw,
            {"mode", "fixture_id", "source_path", "prompt_regime", "provenance"},
            "target source",
        )
        mode = target["mode"]
        if mode not in prepare.MODES or mode in by_mode:
            raise IntegrationError(f"duplicate or unknown source target mode: {mode!r}")
        if target["prompt_regime"] != prepare.PROMPT_REGIMES[mode]:
            raise IntegrationError(f"prompt regime mismatch for target {mode}")
        relative(target["source_path"], f"{mode} source_path")
        by_mode[mode] = target
    if set(by_mode) != set(prepare.MODES):
        raise IntegrationError("target source mode set is incomplete")
    if production and (
        by_mode["P"]["source_path"] != "fixtures/v4-focused/p_predicates"
        or by_mode["P"]["provenance"] != "REUSED_UNCHANGED_FROM_V4_FOCUSED"
    ):
        raise IntegrationError("P must bind the unchanged V4 focused target source")
    return declaration


def trusted_production_declaration_bytes() -> bytes:
    """Return the exact production source selection from the trusted harness.

    A candidate's embedded copy is evidence, not authority.  Production
    verification always starts from this separately trusted installation.
    """

    if SOURCE_DECLARATION.is_symlink() or not SOURCE_DECLARATION.is_file():
        raise IntegrationError("trusted production source declaration is not a regular file")
    data = SOURCE_DECLARATION.read_bytes()
    validate_source_declaration(
        parse_json_bytes(data, str(SOURCE_DECLARATION)), production=True
    )
    return data


def trusted_unsafe_rust_root() -> Path:
    root = RUN.parent.parent
    if root.is_symlink() or not root.is_dir() or root.resolve() != root:
        raise IntegrationError("trusted unsafe-rust source root is not an absolute real directory")
    return root


def trusted_declared_tree(relative_path: str, label: str) -> tuple[Path, str]:
    root = trusted_unsafe_rust_root()
    path = root / relative(relative_path, f"{label} trusted source path")
    try:
        resolved = path.resolve(strict=True)
    except OSError as error:
        raise IntegrationError(f"trusted {label} source cannot be resolved: {path}") from error
    if resolved != path or root not in path.parents:
        raise IntegrationError(f"trusted {label} source escapes or traverses a symlink: {path}")
    reject_unsupported_tree(path, f"trusted {label} source")
    return path, prepare.byte_tree_v1(path)


def validate_execution_config(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != set(ROLE_NAMES):
        raise IntegrationError(f"execution roles must be exactly {ROLE_NAMES}")
    keys = {
        "model",
        "reasoning_effort",
        "sampling",
        "token_budget",
        "token_budget_enforcement",
        "time_budget_seconds",
        "time_budget_enforcement",
        "requested_tools",
        "tool_capability_observation",
        "tool_policy_enforcement",
        "requested_network_access",
        "network_capability_observation",
        "network_policy_enforcement",
        "requested_documentation_access",
        "documentation_capability_observation",
        "documentation_policy_enforcement",
        "requested_hosted_build",
        "hosted_build_capability_observation",
        "hosted_build_policy_enforcement",
    }
    for role, raw in value.items():
        config = exact_object(raw, keys, f"execution config {role}")
        text_fields = keys - {
            "token_budget",
            "time_budget_seconds",
            "requested_tools",
        }
        if any(
            not isinstance(config[key], str) or not config[key].strip()
            for key in text_fields
        ):
            raise IntegrationError(
                f"execution config {role} text fields must be declared nonblank strings"
            )
        if (
            not isinstance(config["requested_tools"], list)
            or not config["requested_tools"]
            or any(
                not isinstance(tool, str) or not tool.strip()
                for tool in config["requested_tools"]
            )
            or len(set(config["requested_tools"]))
            != len(config["requested_tools"])
        ):
            raise IntegrationError(f"execution config {role} has invalid tools")
        if (
            config["token_budget"] is not None
            or config["token_budget_enforcement"] != "UNAVAILABLE_NOT_ENFORCED"
            or config["time_budget_seconds"] is not None
            or config["time_budget_enforcement"] != "UNAVAILABLE_NOT_ENFORCED"
        ):
            raise IntegrationError(
                f"execution config {role} must truthfully record unavailable, unenforced token/time limits"
            )
        for capability in ("tool", "network", "documentation", "hosted_build"):
            if (
                config[f"{capability}_policy_enforcement"]
                != "PROMPT_ONLY_NOT_TECHNICALLY_ENFORCED"
                or config[f"{capability}_capability_observation"]
                != "SESSION_INHERITED_MAY_EXCEED_REQUEST"
            ):
                raise IntegrationError(
                    f"execution config {role} overstates {capability} isolation"
                )
    return value


def validate_reviewed_values(
    value: Any,
    declaration_bytes: bytes,
    *,
    expected_status: str = "READY",
    require_empty_candidate_static: bool = True,
    expected_reviewed_static_base: str | None = None,
) -> dict[str, Any]:
    reviewed = exact_object(
        value,
        {
            "schema_version",
            "status",
            "source_declaration_sha256",
            "authority_packet_path",
            "target_parameters",
            "invocation_blocks",
            "execution_environment",
            "forbidden_tokens",
            "reviewed_static_base",
            "reviewed_static",
        },
        "reviewed values",
    )
    if expected_status not in {"SOURCE-REVIEW-CANDIDATE", "READY"}:
        raise IntegrationError("unknown reviewed-values lifecycle status")
    if reviewed["schema_version"] != 1 or reviewed["status"] != expected_status:
        raise IntegrationError(
            f"reviewed values must be schema-v1 {expected_status}"
        )
    if reviewed["source_declaration_sha256"] != sha256(declaration_bytes):
        raise IntegrationError("reviewed values do not bind the source declaration bytes")
    relative(reviewed["authority_packet_path"], "authority_packet_path")
    parameters = reviewed["target_parameters"]
    if not isinstance(parameters, dict) or set(parameters) != set(prepare.MODES):
        raise IntegrationError("target parameters must cover every mode exactly")
    for mode, raw in parameters.items():
        item = exact_object(raw, {"task_mode", "word_cap"}, f"target parameters {mode}")
        if not isinstance(item["task_mode"], str) or not re.fullmatch(
            r"[a-z][a-z0-9_-]*", item["task_mode"]
        ):
            raise IntegrationError(f"invalid task_mode for {mode}")
        if type(item["word_cap"]) is not int or item["word_cap"] < 1:
            raise IntegrationError(f"invalid word_cap for {mode}")
    blocks = reviewed["invocation_blocks"]
    if not isinstance(blocks, dict) or set(blocks) != set(prepare.CONDITIONS):
        raise IntegrationError("invocation blocks must cover all conditions exactly")
    if blocks["no_skill"] != "":
        raise IntegrationError("no_skill invocation block must be exactly zero bytes")
    for role in ("v5", "v4"):
        if not isinstance(blocks[role], str) or not blocks[role].strip():
            raise IntegrationError(f"{role} invocation block must be reviewed nonblank text")
        if "{{" in blocks[role] or "}}" in blocks[role] or "\0" in blocks[role]:
            raise IntegrationError(f"{role} invocation block contains a forbidden marker")
    validate_execution_config(reviewed["execution_environment"])
    tokens = reviewed["forbidden_tokens"]
    if (
        not isinstance(tokens, list)
        or not tokens
        or any(
            not isinstance(token, str)
            or not token
            or not token.isascii()
            or token != token.lower()
            for token in tokens
        )
        or len(set(tokens)) != len(tokens)
    ):
        raise IntegrationError(
            "forbidden_tokens must be nonblank unique lowercase ASCII strings"
        )
    if not BASELINE_CONTENT_FORBIDDEN_TOKENS.issubset(tokens):
        raise IntegrationError(
            "forbidden_tokens omits the fixed cross-condition content baseline"
        )
    if not isinstance(reviewed["reviewed_static"], list):
        raise IntegrationError("reviewed_static must be a list")
    expected_static_base = expected_reviewed_static_base or (
        REVIEWED_STATIC_DERIVED_BASE
        if expected_status == SOURCE_REVIEW_CANDIDATE_STATUS
        and require_empty_candidate_static
        else REVIEWED_STATIC_CANDIDATE_BASE
    )
    if reviewed["reviewed_static_base"] != expected_static_base:
        raise IntegrationError(
            "reviewed_static_base does not identify the exact record path root"
        )
    if (
        expected_status == SOURCE_REVIEW_CANDIDATE_STATUS
        and require_empty_candidate_static
        and reviewed["reviewed_static"] != []
    ):
        raise IntegrationError(
            "SOURCE-REVIEW-CANDIDATE reviewed_static must be empty; the trusted builder derives it"
        )
    return reviewed


def validate_hook_inventory(root: Path, *, expected_status: str) -> dict[str, Any]:
    value = read_json(root / "integration-hooks.json")
    hooks = exact_object(
        value,
        {"schema_version", "status", "blocking", "failure_gate", "hooks"},
        "integration hook inventory",
    )
    if (
        hooks["schema_version"] != 1
        or hooks["status"] != expected_status
        or hooks["blocking"] is not True
        or hooks["failure_gate"] != "D-STATIC-INTEGRITY"
        or not isinstance(hooks["hooks"], list)
    ):
        raise IntegrationError("integration hook envelope drifted")
    seen: list[str] = []
    for raw in hooks["hooks"]:
        hook = exact_object(
            raw,
            {"id", "phase", "required", "implementation_status", "consumes", "produces"},
            "integration hook",
        )
        hook_id = hook["id"]
        if (
            hook_id not in HOOK_PHASES
            or hook["phase"] != HOOK_PHASES[hook_id]
            or hook["required"] is not True
            or hook["implementation_status"] != HOOK_IMPLEMENTATION[hook_id]
            or not isinstance(hook["consumes"], list)
            or not hook["consumes"]
            or not isinstance(hook["produces"], list)
            or not hook["produces"]
        ):
            raise IntegrationError(f"integration hook contract drifted: {hook_id!r}")
        seen.append(hook_id)
    if seen != list(HOOK_PHASES):
        raise IntegrationError("integration hook order/set drifted")
    validate_schema_file(
        hooks,
        RUN / "schemas" / "integration-hooks.schema.json",
        "integration-hooks.json",
    )
    return hooks


def validate_runtime_policy(root: Path, *, expected_status: str) -> dict[str, Any]:
    policy = exact_object(
        read_json(root / "runtime-policy.json"),
        {
            "schema_version",
            "status",
            "static_manifest_path",
            "static_lock_path",
            "review_snapshot_manifest_path",
            "review_snapshot_descriptor_path",
            "mutable_root",
            "state_root",
            "static_manifest_exclusions",
            "runtime_carve_out",
            "draft_runtime_policy",
            "post_lock_state_policy",
            "agent_io_root_policy",
            "agent_input_leaf",
            "agent_output_leaf",
            "agent_visible_path_forbidden_terms",
            "symlink_policy",
            "seal_copy_policy",
            "output_capture_hard_byte_limit",
            "output_capture_hard_entry_limit",
            "output_capture_hard_path_byte_limit",
            "output_capture_overflow_policy",
            "evidence_policy",
            "fresh_attempt_root_policy",
            "frozen_input_policy",
            "snapshot_policy",
            "bundle_kind_policy",
            "static_manifest_algorithm",
            "path_domain",
            "metadata_policy",
            "synthetic_test_policy",
            "coordinator_claim_policy",
            "evaluator_input_policy",
            "aggregation_stage_policy",
            "successful_attempt_count_policy",
            "terminal_outcome_policy",
            "seal_workspace_policy",
            "same_uid_agent_tcb_policy",
        },
        "runtime policy",
    )
    exact_values = {
        "schema_version": 1,
        "status": expected_status,
        "static_manifest_path": STATIC_MANIFEST,
        "static_lock_path": STATIC_LOCK,
        "review_snapshot_manifest_path": SNAPSHOT_MANIFEST,
        "review_snapshot_descriptor_path": SNAPSHOT_DESCRIPTOR,
        "mutable_root": RUNTIME_ROOT,
        "state_root": RUNTIME_STATE,
        "static_manifest_exclusions": [f"{RUNTIME_STATE}/**"],
        "runtime_carve_out": "EXACT_RUNTIME_STATE_SUBTREE_ONLY",
        "draft_runtime_policy": "FORBIDDEN_UNTIL_VALID_LOCK_AND_STATIC_MANIFEST",
        "post_lock_state_policy": "ONLY_COORDINATOR_STATE_AND_CONTENT_ADDRESSED_ENVELOPES",
        "agent_io_root_policy": "FRESH_EXTERNAL_NEUTRAL_TMP_RANDOM_OPAQUE_ROOT",
        "agent_input_leaf": prepare.INPUT_ALIAS,
        "agent_output_leaf": prepare.OUTPUT_ALIAS,
        "symlink_policy": "FORBIDDEN",
        "seal_copy_policy": "HASH_AND_COPY_EXTERNAL_OUTPUT_INTO_IN_TREE_CANONICAL_STATE",
        "output_capture_hard_byte_limit": 4 * 1024 * 1024,
        "output_capture_hard_entry_limit": 4096,
        "output_capture_hard_path_byte_limit": 256 * 1024,
        "output_capture_overflow_policy": "SPEC_OVERAGES_CAPTURED_UNTIL_HARD_LIMIT_HARD_OVERFLOW_AUTHENTICATED_UNAVAILABLE",
        "evidence_policy": "POST_LOCK_COMMITTED_RUNTIME_STATE_REQUIRED_AT_INTEGRATION",
        "fresh_attempt_root_policy": "EXCLUSIVE_CREATE_ON_LEASE",
        "frozen_input_policy": "NO_MUTATION_AFTER_LOCK",
        "snapshot_policy": "REVIEW_EXACT_STAGED_PAYLOAD_BEFORE_FINALIZATION",
        "bundle_kind_policy": "LOCK_AND_STATUS_MUST_MATCH_CALLER_EXPECTED_KIND",
        "static_manifest_algorithm": MANIFEST_ALGORITHM,
        "path_domain": PATH_DOMAIN,
        "metadata_policy": "STATIC_FILES_0444_STATIC_DIRS_0555_RUNTIME_STATE_0700",
        "synthetic_test_policy": "PRIVATE_PATH_CAN_ONLY_MINT_SYNTHETIC_TEST_ONLY",
        "coordinator_claim_policy": "IMMUTABLE_STATIC_LOCK_BOUND_CLAIM_BEFORE_ANY_SEMANTIC_LEASE",
        "evaluator_input_policy": "ASSIGNMENT_ONLY_FROM_COMMITTED_IMMUTABLE_PREDECESSOR_STAGE",
        "aggregation_stage_policy": "SIX_ATOMIC_NOREPLACE_IMMUTABLE_MANIFEST_BOUND_PREFIX_STAGES",
        "successful_attempt_count_policy": "EXACTLY_154_TO_163_SEALED_ATTEMPTS",
        "terminal_outcome_policy": "FINAL_SUCCESS_OR_AUTHENTICATED_TERMINAL_ERROR_MUTUALLY_EXCLUSIVE",
        "seal_workspace_policy": "EXACT_LEASE_BOUND_INPUT_OUTPUT_TREE_REVALIDATED_UNDER_LOCK_AT_SEAL",
        "same_uid_agent_tcb_policy": "OS_ENFORCED_READ_ONLY_INPUT_OR_SEPARATE_OWNERSHIP_REQUIRED_FOR_TRANSIENT_MUTATION_THREAT",
    }
    for key, expected in exact_values.items():
        if policy[key] != expected:
            raise IntegrationError(f"runtime-policy {key} does not equal {expected!r}")
    terms = policy["agent_visible_path_forbidden_terms"]
    if (
        not isinstance(terms, list)
        or not terms
        or any(
            not isinstance(term, str)
            or not term
            or not term.isascii()
            or term != term.lower()
            for term in terms
        )
        or len(set(terms)) != len(terms)
    ):
        raise IntegrationError(
            "runtime-policy path-forbidden terms must be unique lowercase ASCII strings"
        )
    validate_schema_file(
        policy,
        RUN / "schemas" / "runtime-policy.schema.json",
        "runtime-policy.json",
    )
    return policy


def validate_integration_status(
    root: Path, *, expected_bundle_kind: str
) -> dict[str, Any]:
    status = exact_object(
        read_json(root / "INTEGRATION-STATUS.json"),
        {
            "schema_version",
            "status",
            "bundle_kind",
            "creation_path",
            "phase",
            "static_state",
            "semantic_launch_eligible",
            "semantic_launch_requires_expected_production_verification",
            "runtime_collection_receipts_required_after_lock",
            "postrun_aggregate_receipts_required_after_collection",
        },
        "integration status",
    )
    expected_creation = (
        "PRODUCTION_REVIEWED_SNAPSHOT_FINALIZATION"
        if expected_bundle_kind == "PRODUCTION"
        else "PRIVATE_SYNTHETIC_SELF_TEST_FINALIZATION"
    )
    if status != {
        "schema_version": 1,
        "status": "READY",
        "bundle_kind": expected_bundle_kind,
        "creation_path": expected_creation,
        "phase": "FINALIZE_STATIC_COMPLETE",
        "static_state": "BOUND_BY_ROOT_STATIC_LOCK",
        "semantic_launch_eligible": expected_bundle_kind == "PRODUCTION",
        "semantic_launch_requires_expected_production_verification": True,
        "runtime_collection_receipts_required_after_lock": True,
        "postrun_aggregate_receipts_required_after_collection": True,
    }:
        raise IntegrationError("integration status is not the exact READY contract")
    validate_schema_file(
        status,
        RUN / "schemas" / "integration-status.schema.json",
        "INTEGRATION-STATUS.json",
    )
    return status


def draft() -> None:
    prepare.verify_draft()
    declaration_bytes = SOURCE_DECLARATION.read_bytes()
    validate_source_declaration(
        parse_json_bytes(declaration_bytes, str(SOURCE_DECLARATION)), production=True
    )
    validate_hook_inventory(RUN, expected_status="DRAFT")
    validate_runtime_policy(RUN, expected_status="DRAFT")
    print("V5 DRAFT source and static-integration mechanism validation passed")


def required_review_paths() -> set[str]:
    paths = {
        "freeze/authority/propositions.json",
        "freeze/authority/quotation-locators.json",
        "freeze/authority/verification.json",
        "freeze/authority/agent-visible/common.json",
        "freeze/controls.json",
        "freeze/rules/defect-rules.json",
    }
    for mode in prepare.MODES:
        paths.update(
            {
                f"freeze/atoms/{mode}.json",
                f"freeze/fixtures/{mode}.json",
                f"freeze/oracle/{mode}.md",
                f"freeze/allowlists/{mode}.txt",
            }
        )
    return paths


def source_review_tool_records(tool_root: Path = RUN) -> list[dict[str, str]]:
    """Bind all harness Python and JSON-schema inputs used by source review."""

    tool_root = tool_root.resolve()
    paths = {
        path.relative_to(tool_root).as_posix()
        for path in tool_root.rglob("*.py")
        if "__pycache__" not in path.parts
    }
    schema_root = tool_root / "schemas"
    if schema_root.is_dir():
        paths.update(
            path.relative_to(tool_root).as_posix()
            for path in schema_root.rglob("*.json")
        )
    required = {
        "integrate.py",
        "prepare.py",
        "freeze/validate_controls.py",
        "freeze/validate_fixture_manifests.py",
        "freeze/validate_oracle_materials.py",
        "freeze/authority/validate_agent_visible.py",
        "schemas/source-review-contract.schema.json",
        "schemas/source-review-receipt.schema.json",
        "schemas/source-review-snapshot.schema.json",
    }
    if not required.issubset(paths):
        raise IntegrationError(
            f"source-review tool inventory is incomplete: {sorted(required - paths)}"
        )
    records: list[dict[str, str]] = []
    for path_text in sorted(paths):
        path = tool_root / path_text
        if path.is_symlink() or not path.is_file():
            raise IntegrationError(
                f"source-review tool is not a regular file: {path_text}"
            )
        records.append({"path": path_text, "sha256": sha256(path.read_bytes())})
    return records


def source_review_tool_set_sha256(records: list[dict[str, str]]) -> str:
    return sha256(
        REVIEWER_TOOL_SET_ALGORITHM.encode("ascii")
        + b"\0"
        + canonical_json_bytes(records)
    )


def source_review_procedure_files() -> dict[str, bytes]:
    return {
        f"{SOURCE_REVIEW_PROCEDURE_ROOT}/oracle.md": SOURCE_REVIEW_PROCEDURE_TEXT[
            "INDEPENDENT_ORACLE"
        ].encode("utf-8"),
        f"{SOURCE_REVIEW_PROCEDURE_ROOT}/coherence.md": SOURCE_REVIEW_PROCEDURE_TEXT[
            "COHERENCE"
        ].encode("utf-8"),
        f"{SOURCE_REVIEW_PROCEDURE_ROOT}/source-review-receipt.schema.json": (
            RUN / "schemas" / "source-review-receipt.schema.json"
        ).read_bytes(),
    }


def source_review_theorem_file_map(
    declaration: dict[str, Any],
) -> dict[str, bytes]:
    """Return every regular theorem-input file under its review-copy path."""

    result = {
        f"{SOURCE_REVIEW_THEOREM_ROOT}/source-declaration.json": (
            trusted_production_declaration_bytes()
        )
    }
    for path_text in sorted(required_review_paths()):
        result[
            f"{SOURCE_REVIEW_THEOREM_ROOT}/draft-reviewed-static/{path_text}"
        ] = (RUN / path_text).read_bytes()
    unsafe_rust = trusted_unsafe_rust_root()
    for record in declaration["targets"]:
        source_path = relative(record["source_path"], "source-review target path")
        source_root = unsafe_rust / source_path
        reject_unsupported_tree(source_root, f"source-review target {record['mode']}")
        for source in sorted(source_root.rglob("*"), key=lambda path: path.as_posix()):
            if not source.is_file():
                continue
            relative_file = source.relative_to(source_root).as_posix()
            destination = (
                f"{SOURCE_REVIEW_THEOREM_ROOT}/unsafe-rust/"
                f"{source_path}/{relative_file}"
            )
            if destination in result:
                raise IntegrationError(
                    f"duplicate source-review theorem input: {destination}"
                )
            result[destination] = source.read_bytes()
    return result


def source_review_support_file_map(
    declaration: dict[str, Any],
) -> dict[str, bytes]:
    return {
        **source_review_procedure_files(),
        **source_review_theorem_file_map(declaration),
    }


def materialize_source_review_support(
    root: Path, declaration: dict[str, Any]
) -> None:
    for path_text, data in source_review_procedure_files().items():
        write_exclusive(root / path_text, data)
    write_exclusive(
        root / SOURCE_REVIEW_THEOREM_ROOT / "source-declaration.json",
        trusted_production_declaration_bytes(),
    )
    for path_text in sorted(required_review_paths()):
        write_exclusive(
            root
            / SOURCE_REVIEW_THEOREM_ROOT
            / "draft-reviewed-static"
            / path_text,
            (RUN / path_text).read_bytes(),
        )
    unsafe_rust = trusted_unsafe_rust_root()
    for record in declaration["targets"]:
        source_path = relative(record["source_path"], "source-review target path")
        copy_tree(
            unsafe_rust / source_path,
            root / SOURCE_REVIEW_THEOREM_ROOT / "unsafe-rust" / source_path,
        )


def reject_reviewed_static_residue(root: Path) -> None:
    """Reject source-phase status residue without banning legitimate prose."""

    stale_json_values = {
        "DRAFT",
        "DRAFT_VERIFIED_PENDING_CROSS_REVIEW",
        "VERIFIED_PENDING_CROSS_REVIEW",
        "INTEGRATION_BOUND_SOURCE_TREE_SHA256",
        "INTEGRATION_BOUND_EXACT_REPORT_MATERIAL_SET_SHA256",
    }

    def walk(value: Any, label: str) -> None:
        if isinstance(value, dict):
            for key, item in value.items():
                walk(item, f"{label}.{key}")
            return
        if isinstance(value, list):
            for index, item in enumerate(value):
                walk(item, f"{label}[{index}]")
            return
        if isinstance(value, str) and (
            value in stale_json_values
            or value.startswith("DRAFT_")
            or value.endswith("_PENDING_CROSS_REVIEW")
        ):
            raise IntegrationError(f"reviewed static retains source-DRAFT residue: {label}")

    for path_text in sorted(required_review_paths()):
        path = root / path_text
        if path.suffix == ".json":
            walk(read_json(path), path_text)
        elif path_text.startswith("freeze/oracle/"):
            text_value = path.read_text(encoding="utf-8")
            if "**DRAFT / evaluator-only.**" in text_value:
                raise IntegrationError(f"reviewed oracle retains its DRAFT marker: {path_text}")
            if "**SOURCE-REVIEW-CANDIDATE / evaluator-only.**" not in text_value:
                raise IntegrationError(
                    f"reviewed oracle lacks its exact candidate marker: {path_text}"
                )
            if "**READY / evaluator-only.**" in text_value:
                raise IntegrationError(
                    f"reviewed oracle prematurely claims READY: {path_text}"
                )


def validate_reviewed_semantic_closure(
    root: Path,
    *,
    expected_fixture_phase: str,
    expected_source_digests: dict[str, str],
    expected_report_material_digests: dict[str, str] | None = None,
    evidence_source_root: Path | None = None,
) -> None:
    """Run the trusted semantic validators over reviewed or derived bytes."""

    freeze = root / "freeze"
    semantic_status = (
        SOURCE_REVIEW_CANDIDATE_STATUS
        if expected_fixture_phase == "SOURCE_REVIEW_CANDIDATE"
        else "READY"
    )
    try:
        runpy.run_path(
            str(RUN / "freeze" / "validate_controls.py"),
            run_name="v5_integration_controls",
        )["validate"](freeze, expected_status=semantic_status)
        runpy.run_path(
            str(RUN / "freeze" / "validate_fixture_manifests.py"),
            run_name="v5_integration_fixtures",
        )["validate"](
            freeze,
            unsafe_rust_root=trusted_unsafe_rust_root(),
            expected_phase=expected_fixture_phase,
            expected_source_digests=expected_source_digests,
            expected_report_material_digests=expected_report_material_digests,
        )
        runpy.run_path(
            str(RUN / "freeze" / "validate_oracle_materials.py"),
            run_name="v5_integration_oracles",
        )["validate"](
            freeze,
            expected_status=semantic_status,
            repository_root=(
                trusted_unsafe_rust_root().parents[1]
                if evidence_source_root is None
                else None
            ),
            supplied_source_root=evidence_source_root,
        )
        projection_digest = runpy.run_path(
            str(RUN / "freeze" / "authority" / "validate_agent_visible.py"),
            run_name="v5_integration_authority_projection",
        )["validate"](freeze / "authority", expected_status=semantic_status)
    except (AssertionError, ValueError, KeyError, TypeError) as error:
        raise IntegrationError("reviewed static semantic closure failed") from error
    packet = freeze / "authority" / "agent-visible" / "common.json"
    if projection_digest != sha256(packet.read_bytes()):
        raise IntegrationError("reviewed authority projection digest mismatch")
    for mode in prepare.MODES:
        validate_schema_file(
            read_json(freeze / "fixtures" / f"{mode}.json"),
            RUN / "schemas" / "fixture-manifest.schema.json",
            f"reviewed fixture manifest {mode}",
        )


def validate_reviewed_static(
    root: Path,
    records: Any,
    *,
    expected_decision: str = "PASS",
) -> None:
    if expected_decision not in {"PENDING", "PASS"}:
        raise IntegrationError("reviewed static expected decision is unknown")
    if not isinstance(records, list):
        raise IntegrationError("reviewed_static must be a list")
    observed: set[str] = set()
    for raw in records:
        record = exact_object(raw, {"path", "sha256", "decision"}, "static review")
        path_text = relative(record["path"], "static review path")
        if path_text in observed:
            raise IntegrationError(f"duplicate static review path: {path_text}")
        observed.add(path_text)
        if record["decision"] != expected_decision:
            raise IntegrationError(
                f"static review has wrong {expected_decision} phase: {path_text}"
            )
        path = root / path_text
        if path.is_symlink() or not path.is_file():
            raise IntegrationError(f"reviewed static path is not a regular file: {path_text}")
        if sha256(path.read_bytes()) != digest(record["sha256"], f"review {path_text}"):
            raise IntegrationError(f"reviewed static digest mismatch: {path_text}")
        if path.suffix == ".json":
            value = read_json(path)
            if path_text == "freeze/authority/agent-visible/common.json":
                if (
                    not isinstance(value, dict)
                    or value.get("schema") != "rust-documentation-excerpts-v1"
                ):
                    raise IntegrationError(
                        "reviewed agent-visible authority packet has the wrong schema"
                    )
                continue
            expected_status = SOURCE_REVIEW_CANDIDATE_STATUS
            if not isinstance(value, dict) or value.get("status") != expected_status:
                raise IntegrationError(
                    f"reviewed JSON has wrong lifecycle status: {path_text}"
                )
    expected = required_review_paths()
    if observed != expected:
        missing = sorted(expected - observed)
        extra = sorted(observed - expected)
        raise IntegrationError(f"static review path set mismatch; missing={missing}, extra={extra}")
    reject_reviewed_static_residue(root)


def source_review_artifacts(root: Path) -> list[dict[str, str]]:
    values = read_json(root / "reviewed-values.json")
    authority_path = relative(values["authority_packet_path"], "authority packet path")
    paths = {
        "reviewed-values.json",
        "seeds.json",
        authority_path,
        *(f"reviewed-static/{path}" for path in required_review_paths()),
        *(
            path.relative_to(root).as_posix()
            for support_root in (
                root / SOURCE_REVIEW_PROCEDURE_ROOT,
                root / SOURCE_REVIEW_THEOREM_ROOT,
            )
            for path in support_root.rglob("*")
            if path.is_file()
        ),
    }
    artifacts: list[dict[str, str]] = []
    for path_text in sorted(paths):
        path = root / path_text
        if path.is_symlink() or not path.is_file():
            raise IntegrationError(f"source-review artifact is not a regular file: {path_text}")
        artifacts.append({"path": path_text, "sha256": sha256(path.read_bytes())})
    return artifacts


def source_review_coverage_items(
    root: Path, review_kind: str
) -> list[dict[str, str]]:
    reviewed_root = root / "reviewed-static" / "freeze"
    items: list[dict[str, str]] = []
    if review_kind == "INDEPENDENT_ORACLE":
        for mode in prepare.MODES:
            atoms = read_json(reviewed_root / "atoms" / f"{mode}.json")["atoms"]
            for atom in atoms:
                items.append(
                    {
                        "id": f"atom:{atom['id']}",
                        "subject": atom["direct_criterion"],
                    }
                )
        locators = read_json(
            reviewed_root / "authority" / "quotation-locators.json"
        )["records"]
        for locator_index, locator in enumerate(locators, start=1):
            for edge_index, url in enumerate(locator["urls"], start=1):
                items.append(
                    {
                        "id": (
                            f"quotation:{locator_index:03d}:{edge_index:02d}:"
                            f"{locator['authority_id']}"
                        ),
                        "subject": f"{url} | {locator['exact_excerpt']}",
                    }
                )
        authority_entries = read_json(
            reviewed_root / "authority" / "propositions.json"
        )["entries"]
        for entry in authority_entries:
            items.append(
                {
                    "id": f"authority-proposition:{entry['id']}",
                    "subject": (
                        f"{entry['proposition']} | applicability={entry['applicability']} | "
                        f"consumers={','.join(entry['consumers'])}"
                    ),
                }
            )
        for mode in prepare.MODES:
            oracle_bytes = (reviewed_root / "oracle" / f"{mode}.md").read_bytes()
            items.append(
                {
                    "id": f"oracle-conclusions:{mode}",
                    "subject": f"mode={mode} oracle_sha256={sha256(oracle_bytes)}",
                }
            )
        declaration = read_json(
            root / SOURCE_REVIEW_THEOREM_ROOT / "source-declaration.json"
        )
        fixture_by_mode = {
            mode: read_json(reviewed_root / "fixtures" / f"{mode}.json")
            for mode in prepare.MODES
        }
        for target in declaration["targets"]:
            mode = target["mode"]
            fixture = fixture_by_mode[mode]
            items.append(
                {
                    "id": f"target-source-join:{mode}",
                    "subject": (
                        f"fixture={target['fixture_id']} source={target['source_path']} "
                        f"tree={fixture['source_tree_algorithm']}:"
                        f"{fixture['source_tree_sha256']}"
                    ),
                }
            )
    elif review_kind == "COHERENCE":
        for path_text in sorted(required_review_paths()):
            items.append(
                {"id": f"reviewed-path:{path_text}", "subject": path_text}
            )
        controls = read_json(reviewed_root / "controls.json")["controls"]
        for control in controls:
            items.append(
                {
                    "id": f"control:{control['id']}",
                    "subject": control["rationale"],
                }
            )
        authority_entries = read_json(
            reviewed_root / "authority" / "propositions.json"
        )["entries"]
        for mode in prepare.MODES:
            atoms = read_json(reviewed_root / "atoms" / f"{mode}.json")["atoms"]
            for atom in atoms:
                for prerequisite in atom["prerequisites"]:
                    items.append(
                        {
                            "id": f"prerequisite:{atom['id']}:{prerequisite}",
                            "subject": f"{atom['id']} immediately requires {prerequisite}",
                        }
                    )
        for entry in authority_entries:
            for consumer in entry["consumers"]:
                items.append(
                    {
                        "id": f"authority-consumer:{entry['id']}:{consumer}",
                        "subject": f"{entry['id']} is consumed by {consumer}",
                    }
                )
        for mode in prepare.MODES:
            allowlist = (
                reviewed_root / "allowlists" / f"{mode}.txt"
            ).read_text(encoding="utf-8").splitlines()
            for index, url in enumerate(allowlist, start=1):
                items.append(
                    {
                        "id": f"allowlist:{mode}:{index:03d}",
                        "subject": url,
                    }
                )
            fixture = read_json(reviewed_root / "fixtures" / f"{mode}.json")
            for index, surface in enumerate(fixture["scoped_surfaces"], start=1):
                items.append(
                    {
                        "id": f"fixture-surface:{mode}:{index:02d}",
                        "subject": surface,
                    }
                )
            for index, supported in enumerate(fixture["supported_set"], start=1):
                items.append(
                    {
                        "id": f"supported-set:{mode}:{index:02d}",
                        "subject": supported,
                    }
                )
        declaration = read_json(
            root / SOURCE_REVIEW_THEOREM_ROOT / "source-declaration.json"
        )
        for target in declaration["targets"]:
            items.append(
                {
                    "id": f"mode-fixture-source-join:{target['mode']}",
                    "subject": (
                        f"mode={target['mode']} fixture={target['fixture_id']} "
                        f"source={target['source_path']}"
                    ),
                }
            )

        def collect_rules(value: Any) -> None:
            if isinstance(value, dict):
                if isinstance(value.get("id"), str) and isinstance(
                    value.get("criterion"), str
                ):
                    items.append(
                        {
                            "id": f"defect-rule:{value['id']}",
                            "subject": value["criterion"],
                        }
                    )
                for child in value.values():
                    collect_rules(child)
            elif isinstance(value, list):
                for child in value:
                    collect_rules(child)

        collect_rules(read_json(reviewed_root / "rules" / "defect-rules.json"))
    else:
        raise IntegrationError(f"unknown source-review kind: {review_kind}")
    if (
        not items
        or len({item["id"] for item in items}) != len(items)
        or any(not item["subject"].strip() for item in items)
    ):
        raise IntegrationError("source-review coverage inventory is not exact")
    return items


def derive_source_review_contracts(
    root: Path, *, tool_root: Path = RUN
) -> dict[str, dict[str, Any]]:
    artifacts = source_review_artifacts(root)
    artifact_set_sha256 = sha256(canonical_json_bytes(artifacts))
    reviewed = read_json(root / "reviewed-values.json")
    static_set_sha256 = sha256(canonical_json_bytes(reviewed["reviewed_static"]))
    theorem_artifacts = [
        artifact
        for artifact in artifacts
        if artifact["path"].startswith(f"{SOURCE_REVIEW_THEOREM_ROOT}/")
    ]
    theorem_input_set_sha256 = sha256(canonical_json_bytes(theorem_artifacts))
    reviewer_tools = source_review_tool_records(tool_root)
    reviewer_tool_set_sha256 = source_review_tool_set_sha256(reviewer_tools)
    evidence_bindings = {
        "exact_quotation_evidence_algorithm": EXACT_QUOTATION_EVIDENCE_ALGORITHM,
        "exact_quotation_evidence_sha256": EXACT_QUOTATION_EVIDENCE_SHA256,
        "reviewed_source_transition_algorithm": SOURCE_REVIEW_TRANSITION_ALGORITHM,
        "reviewed_static_set_algorithm": REVIEWED_STATIC_SET_ALGORITHM,
        "reviewed_static_set_sha256": static_set_sha256,
        "theorem_input_set_sha256": theorem_input_set_sha256,
    }
    result: dict[str, dict[str, Any]] = {}
    for name, review_kind in SOURCE_REVIEW_KINDS:
        coverage_items = source_review_coverage_items(root, review_kind)
        procedure_path = (
            f"{SOURCE_REVIEW_PROCEDURE_ROOT}/oracle.md"
            if review_kind == "INDEPENDENT_ORACLE"
            else f"{SOURCE_REVIEW_PROCEDURE_ROOT}/coherence.md"
        )
        receipt_schema_path = (
            f"{SOURCE_REVIEW_PROCEDURE_ROOT}/source-review-receipt.schema.json"
        )
        contract = {
            "schema_version": 1,
            "status": "READY",
            "review_kind": review_kind,
            "procedure_id": f"v5-source-review/{Path(name).stem}",
            "procedure_version": SOURCE_REVIEW_PROCEDURE_VERSION,
            "procedure_path": procedure_path,
            "procedure_sha256": sha256((root / procedure_path).read_bytes()),
            "receipt_schema_path": receipt_schema_path,
            "receipt_schema_sha256": sha256(
                (root / receipt_schema_path).read_bytes()
            ),
            "reviewer_tool_set_algorithm": REVIEWER_TOOL_SET_ALGORITHM,
            "reviewer_tools": reviewer_tools,
            "reviewer_tool_set_sha256": reviewer_tool_set_sha256,
            "reviewer_runtime_attestation_algorithm": (
                REVIEWER_RUNTIME_ATTESTATION_ALGORITHM
            ),
            "custody_requirement": "VERIFIED_PRIVATE_COPY_AND_END_REVERIFY",
            "required_check_ids": list(SOURCE_REVIEW_CHECK_IDS[review_kind]),
            "coverage_items": coverage_items,
            "coverage_set_algorithm": REVIEW_COVERAGE_SET_ALGORITHM,
            "coverage_set_sha256": review_coverage_set_sha256(coverage_items),
            "artifacts": artifacts,
            "artifact_set_sha256": artifact_set_sha256,
            "evidence_bindings": evidence_bindings,
        }
        validate_schema_file(
            contract,
            RUN / "schemas" / "source-review-contract.schema.json",
            f"source review contract {name}",
        )
        result[name] = contract
    return result


def build_source_review_contracts(root: Path) -> dict[str, dict[str, Any]]:
    contracts = derive_source_review_contracts(root)
    for name, contract in contracts.items():
        write_json(root / SOURCE_REVIEW_CONTRACT_ROOT / name, contract)
    return contracts


def validate_source_review_contracts(
    root: Path, *, tool_root: Path = RUN
) -> dict[str, dict[str, Any]]:
    contract_root = root / SOURCE_REVIEW_CONTRACT_ROOT
    if contract_root.is_symlink() or not contract_root.is_dir():
        raise IntegrationError("source-review contract root must be a real directory")
    expected_names = {name for name, _kind in SOURCE_REVIEW_KINDS}
    observed = {path.name for path in contract_root.iterdir() if path.is_file()}
    if observed != expected_names or any(
        path.is_dir() or path.is_symlink() for path in contract_root.iterdir()
    ):
        raise IntegrationError("source-review contract inventory is not exact")
    expected = derive_source_review_contracts(root, tool_root=tool_root)
    for name, contract in expected.items():
        if read_json(contract_root / name) != contract:
            raise IntegrationError(f"source-review contract drifted: {name}")
    return expected


def validate_source_review_result(
    value: Any,
    *,
    label: str,
    review_kind: str,
    contract: dict[str, Any],
    descriptor_sha256: str,
    manifest_sha256: str,
    payload_sha256: str,
    expected_inputs: dict[str, str],
) -> dict[str, Any]:
    """Validate only reviewer-authored source-review findings and evidence."""

    result = exact_object(value, {"summary", "checks"}, label)
    if not isinstance(result["summary"], str) or len(result["summary"].strip()) < 20:
        raise IntegrationError("source review summary is not detailed")
    checks = result["checks"]
    if not isinstance(checks, list) or [
        item.get("id") if isinstance(item, dict) else None for item in checks
    ] != contract["required_check_ids"]:
        raise IntegrationError("source review check inventory is not exact")
    evidence: dict[str, str] = {}
    for item in checks:
        check = exact_object(
            item, {"id", "status", "evidence"}, "source review check"
        )
        if (
            check["status"] != "PASS"
            or not isinstance(check["evidence"], str)
            or len(check["evidence"].strip()) < 20
        ):
            raise IntegrationError("source review check evidence is invalid")
        evidence[check["id"]] = check["evidence"]
    contract_path = f"{SOURCE_REVIEW_CONTRACT_ROOT}/{Path(label).name}"
    required_evidence: dict[str, tuple[str, ...]] = {
        "EXACT-SOURCE-REVIEW-BOUND": (descriptor_sha256, payload_sha256),
        "REVIEW-CONTRACT-BOUND": (
            expected_inputs[contract_path],
            contract["procedure_sha256"],
            contract["receipt_schema_sha256"],
            contract["procedure_version"],
            contract["reviewer_tool_set_algorithm"],
            contract["reviewer_tool_set_sha256"],
            contract["coverage_set_algorithm"],
            contract["coverage_set_sha256"],
            contract["reviewer_runtime_attestation_algorithm"],
        ),
        "ARTIFACT-INVENTORY-CHECKED": (contract["artifact_set_sha256"],),
        "END-OF-REVIEW-REVERIFIED": (manifest_sha256, payload_sha256),
    }
    if review_kind == "INDEPENDENT_ORACLE":
        required_evidence.update(
            {
                "EXACT-QUOTATIONS-AND-PAGE-BYTES-VERIFIED": (
                    EXACT_QUOTATION_EVIDENCE_ALGORITHM,
                    EXACT_QUOTATION_EVIDENCE_SHA256,
                ),
                "ORACLE-ENTAILMENT-CHECKED": (
                    SOURCE_REVIEW_TRANSITION_ALGORITHM,
                    contract["evidence_bindings"]["theorem_input_set_sha256"],
                ),
                "AUTHORITY-PROJECTION-CHECKED": (
                    contract["evidence_bindings"]["reviewed_static_set_sha256"],
                ),
            }
        )
    else:
        required_evidence.update(
            {
                "CONTROL-AND-DEFECT-COVERAGE-CHECKED": (
                    contract["evidence_bindings"]["reviewed_static_set_sha256"],
                ),
                "CROSS-FILE-CLOSURE-CHECKED": (
                    SOURCE_REVIEW_TRANSITION_ALGORITHM,
                ),
                "TRANSFORMATION-CORRECTNESS-CHECKED": (
                    REVIEWED_STATIC_SET_ALGORITHM,
                    contract["evidence_bindings"]["reviewed_static_set_sha256"],
                    contract["evidence_bindings"]["theorem_input_set_sha256"],
                ),
            }
        )
    for check_id, needles in required_evidence.items():
        if any(needle not in evidence[check_id] for needle in needles):
            raise IntegrationError(
                f"source review lacks exact evidence binding {label}.{check_id}"
            )
    return result


def _validate_source_review_receipts_captured(
    receipt_root: Path,
    *,
    snapshot_root: Path,
    descriptor_sha256: str,
    manifest_sha256: str,
    payload_sha256: str,
    synthetic_capability: object | None = None,
) -> tuple[dict[str, dict[str, Any]], dict[str, bytes]]:
    if synthetic_capability not in {None, _SYNTHETIC_CAPABILITY}:
        raise IntegrationError("unrecognized synthetic source-review capability")
    if receipt_root.is_symlink() or not receipt_root.is_dir():
        raise IntegrationError("source-review receipt root must be a real directory")
    reject_unsupported_tree(receipt_root, "source-review receipt root")
    entries = list(receipt_root.iterdir())
    observed = {
        path.name
        for path in entries
        if stat.S_ISREG(path.lstat().st_mode)
    }
    expected = {name for name, _kind in SOURCE_REVIEW_KINDS}
    if observed != expected or len(entries) != len(expected):
        raise IntegrationError("source-review receipt inventory is not exact")
    contracts = validate_source_review_contracts(snapshot_root)
    reviews: list[dict[str, Any]] = []
    captured_bytes: dict[str, bytes] = {}
    for index, (name, review_kind) in enumerate(SOURCE_REVIEW_KINDS):
        raw_review, raw_bytes = capture_review_receipt_json(
            receipt_root / name,
            f"independent source review {index}",
            synthetic_capability=synthetic_capability,
        )
        captured_bytes[name] = raw_bytes
        review = exact_object(
            raw_review,
            {
                "schema_version",
                "status",
                "review_kind",
                "actor",
                "reviewer_runtime",
                "input_digests",
                "output_digests",
                "work_product",
                "result",
            },
            f"independent source review {index}",
        )
        contract = contracts[name]
        actor = exact_object(
            review["actor"],
            {"identity", "role", "implementation", "version"},
            f"source review actor {index}",
        )
        if (
            review["schema_version"] != 1
            or review["status"]
            != (
                "SYNTHETIC-TEST-ONLY"
                if synthetic_capability is _SYNTHETIC_CAPABILITY
                else "PASS"
            )
            or review["review_kind"] != review_kind
            or actor["role"] != "INDEPENDENT_REVIEWER"
            or actor["implementation"] != contract["procedure_id"]
            or actor["version"] != contract["procedure_version"]
        ):
            raise IntegrationError(f"invalid independent source review {index}")
        identity = require_actor_id(actor["identity"], f"source review actor {index}")
        if identity.startswith("synthetic-") and synthetic_capability is not _SYNTHETIC_CAPABILITY:
            raise IntegrationError("synthetic source-review receipt cannot authorize production")
        reviewer_runtime = validate_reviewer_runtime_attestation(
            review["reviewer_runtime"]
        )
        if (
            reviewer_runtime["algorithm"]
            != contract["reviewer_runtime_attestation_algorithm"]
        ):
            raise IntegrationError("source reviewer runtime algorithm drifted")
        work_product, work_product_sha256 = validate_review_work_product(
            review["work_product"],
            expected_coverage_items=contract["coverage_items"],
        )
        contract_path = f"{SOURCE_REVIEW_CONTRACT_ROOT}/{name}"
        expected_inputs = {
            SOURCE_REVIEW_DESCRIPTOR: descriptor_sha256,
            SOURCE_REVIEW_MANIFEST: manifest_sha256,
            contract_path: sha256((snapshot_root / contract_path).read_bytes()),
            contract["procedure_path"]: contract["procedure_sha256"],
            contract["receipt_schema_path"]: contract["receipt_schema_sha256"],
            "trusted-reviewer-tool-set": contract[
                "reviewer_tool_set_sha256"
            ],
            "reviewer-runtime-attestation": sha256(
                canonical_json_bytes(reviewer_runtime)
            ),
        }
        if review["input_digests"] != expected_inputs:
            raise IntegrationError("source review does not bind the exact immutable subject")
        if review["output_digests"] != {
            "reviewed-payload-manifest": payload_sha256,
            "reviewed-artifact-set": contract["artifact_set_sha256"],
            "review-work-product": work_product_sha256,
        }:
            raise IntegrationError("source review output binding is not exact")
        validate_source_review_result(
            review["result"],
            label=name,
            review_kind=review_kind,
            contract=contract,
            descriptor_sha256=descriptor_sha256,
            manifest_sha256=manifest_sha256,
            payload_sha256=payload_sha256,
            expected_inputs=expected_inputs,
        )
        validate_schema_file(
            review,
            RUN / "schemas" / "source-review-receipt.schema.json",
            f"source review receipt {name}",
        )
        reviews.append(review)
    if len({review["actor"]["identity"] for review in reviews}) != 3:
        raise IntegrationError("source reviewer identities must be pairwise distinct")
    validated = {
        name: review for (name, _kind), review in zip(SOURCE_REVIEW_KINDS, reviews)
    }
    return validated, captured_bytes


def validate_source_review_receipts(
    receipt_root: Path,
    *,
    snapshot_root: Path,
    descriptor_sha256: str,
    manifest_sha256: str,
    payload_sha256: str,
    synthetic_capability: object | None = None,
) -> dict[str, dict[str, Any]]:
    validated, _captured_bytes = _validate_source_review_receipts_captured(
        receipt_root,
        snapshot_root=snapshot_root,
        descriptor_sha256=descriptor_sha256,
        manifest_sha256=manifest_sha256,
        payload_sha256=payload_sha256,
        synthetic_capability=synthetic_capability,
    )
    return validated


def trusted_target_source_digests(declaration: dict[str, Any]) -> dict[str, str]:
    result: dict[str, str] = {}
    for record in declaration["targets"]:
        _path, tree_sha256 = trusted_declared_tree(
            record["source_path"], f"{record['mode']} target"
        )
        result[record["mode"]] = tree_sha256
    if set(result) != set(prepare.MODES):
        raise IntegrationError("trusted target digest set is incomplete")
    return result


def derive_reviewed_static_files(
    *, target_source_digests: dict[str, str]
) -> dict[str, bytes]:
    """Mechanically derive honest reviewed-source bytes from DRAFT templates."""

    if set(target_source_digests) != set(prepare.MODES):
        raise IntegrationError("reviewed-source target digests must cover every mode")
    result: dict[str, bytes] = {}
    for path_text in sorted(required_review_paths()):
        source = RUN / path_text
        if source.is_symlink() or not source.is_file():
            raise IntegrationError(f"reviewed-source template is not a regular file: {path_text}")
        if source.suffix == ".json" and path_text != "freeze/authority/agent-visible/common.json":
            value = read_json(source)
            if (
                not isinstance(value, dict)
                or (
                    value.get("status") != "DRAFT"
                    and path_text != "freeze/authority/verification.json"
                )
            ):
                raise IntegrationError(f"reviewed-source JSON template is not DRAFT: {path_text}")
            value = dict(value)
            if path_text.startswith("freeze/fixtures/"):
                mode = Path(path_text).stem
                value.update(
                    {
                        "status": SOURCE_REVIEW_CANDIDATE_STATUS,
                        "source_tree_algorithm": prepare.BYTE_TREE_ALGORITHM,
                        "source_tree_sha256": target_source_digests[mode],
                        "report_material_set_algorithm": REPORT_MATERIAL_SET_ALGORITHM,
                        "exact_report_material_set_sha256": REVIEWED_DERIVATION_SENTINEL,
                    }
                )
            elif path_text == "freeze/authority/propositions.json":
                value["status"] = SOURCE_REVIEW_CANDIDATE_STATUS
                value["verification"] = {
                    "status": "PENDING_INDEPENDENT_SOURCE_REVIEW",
                    "ledger": "verification.json",
                    "ready_for_freeze": False,
                }
            elif path_text == "freeze/authority/verification.json":
                if value.get("status") != "DRAFT_VERIFIED_PENDING_CROSS_REVIEW":
                    raise IntegrationError("authority verification template is not pending review")
                value["status"] = SOURCE_REVIEW_CANDIDATE_STATUS
                value["ready_for_freeze"] = False
                value["pending"] = [
                    "two independent V5 oracle source-review receipts",
                    "one independent V5 coherence source-review receipt",
                    "snapshot derivation of exact report-material bindings",
                ]
            else:
                value["status"] = SOURCE_REVIEW_CANDIDATE_STATUS
            result[path_text] = pretty_json_bytes(value)
        elif path_text.startswith("freeze/oracle/"):
            data = source.read_bytes()
            marker = b"**DRAFT / evaluator-only.**"
            if data.count(marker) != 1:
                raise IntegrationError(f"oracle template lacks one exact DRAFT marker: {path_text}")
            result[path_text] = data.replace(
                marker,
                b"**SOURCE-REVIEW-CANDIDATE / evaluator-only.**",
                1,
            )
        else:
            result[path_text] = source.read_bytes()
    return result


def reviewed_static_records(
    files: dict[str, bytes], *, decision: str = "PASS"
) -> list[dict[str, str]]:
    if set(files) != required_review_paths():
        raise IntegrationError("reviewed static derived file set is not exact")
    if decision not in {"PENDING", "PASS"}:
        raise IntegrationError("reviewed static record decision is unknown")
    return [
        {"path": path, "sha256": sha256(files[path]), "decision": decision}
        for path in sorted(files)
    ]


def derive_ready_reviewed_source_files(
    reviewed_source_root: Path,
) -> dict[str, bytes]:
    """Promote the receipt-reviewed candidate bytes without semantic edits.

    The independent source reviews attest the immutable candidate bytes.  This
    deterministic transition changes lifecycle labels only; report-material
    fixture bindings are derived separately after prompt/plan/launch creation.
    """

    result: dict[str, bytes] = {}
    for path_text in sorted(required_review_paths()):
        if path_text.startswith("freeze/fixtures/"):
            continue
        source = reviewed_source_root / path_text
        if source.is_symlink() or not source.is_file():
            raise IntegrationError(
                f"reviewed-source promotion input is not a regular file: {path_text}"
            )
        data = source.read_bytes()
        if source.suffix == ".json" and path_text != "freeze/authority/agent-visible/common.json":
            value = read_json(source)
            if (
                not isinstance(value, dict)
                or value.get("status") != SOURCE_REVIEW_CANDIDATE_STATUS
            ):
                raise IntegrationError(
                    f"reviewed-source promotion input has wrong status: {path_text}"
                )
            value = dict(value)
            if path_text == "freeze/authority/propositions.json":
                if value.get("verification") != {
                    "status": "PENDING_INDEPENDENT_SOURCE_REVIEW",
                    "ledger": "verification.json",
                    "ready_for_freeze": False,
                }:
                    raise IntegrationError(
                        "authority proposition candidate overstates its review state"
                    )
                value["status"] = "READY"
                value["verification"] = {
                    "status": "VERIFIED",
                    "ledger": "verification.json",
                    "ready_for_freeze": True,
                }
            elif path_text == "freeze/authority/verification.json":
                review = value.get("current_v5_source_review")
                if (
                    not isinstance(review, dict)
                    or review.get("status")
                    != "PENDING_INDEPENDENT_SOURCE_REVIEW"
                ):
                    raise IntegrationError(
                        "authority verification candidate lacks pending V5 review"
                    )
                value["status"] = "READY_VERIFIED"
                value["ready_for_freeze"] = True
                value["pending"] = []
                value["current_v5_source_review"] = {
                    **review,
                    "status": "VERIFIED_BY_INDEPENDENT_SOURCE_REVIEW_RECEIPTS",
                }
            else:
                value["status"] = "READY"
            result[path_text] = pretty_json_bytes(value)
        elif path_text.startswith("freeze/oracle/"):
            marker = b"**SOURCE-REVIEW-CANDIDATE / evaluator-only.**"
            if data.count(marker) != 1:
                raise IntegrationError(
                    f"oracle source-review candidate marker is not exact: {path_text}"
                )
            result[path_text] = data.replace(
                marker, b"**READY / evaluator-only.**", 1
            )
        else:
            result[path_text] = data
    return result


def install_ready_reviewed_source_files(
    stage: Path, reviewed_source_root: Path
) -> None:
    for path_text, data in derive_ready_reviewed_source_files(
        reviewed_source_root
    ).items():
        replace_snapshot_build_bytes(stage / path_text, data)


def require_exact_ready_reviewed_source_files(
    root: Path, reviewed_source_root: Path
) -> None:
    expected = derive_ready_reviewed_source_files(reviewed_source_root)
    for path_text, data in expected.items():
        path = root / path_text
        if path.is_symlink() or not path.is_file() or path.read_bytes() != data:
            raise IntegrationError(
                f"READY reviewed-source promotion drifted: {path_text}"
            )


def reviewable_snapshot_files(root: Path) -> set[str]:
    """Return the exact pre-snapshot file inventory available to reviewers.

    Review contracts, snapshot/finalization records, and runtime state are
    excluded because they either depend on this inventory or are added after
    semantic review.  Every other regular file is assigned to at least one
    hook-specific review contract below.
    """

    excluded_roots = {
        RUNTIME_ROOT,
        "static/integration/review-contracts",
        "static/integration-receipts",
    }
    excluded_files = {
        SNAPSHOT_DESCRIPTOR,
        SNAPSHOT_MANIFEST,
        STATIC_MANIFEST,
        STATIC_LOCK,
        "INTEGRATION-STATUS.json",
    }
    result: set[str] = set()
    for path in root.rglob("*"):
        relative_path = path.relative_to(root).as_posix()
        if relative_path in excluded_files or any(
            relative_path == prefix or relative_path.startswith(f"{prefix}/")
            for prefix in excluded_roots
        ):
            continue
        if path.is_symlink() or not (path.is_file() or path.is_dir()):
            raise IntegrationError(
                f"unsupported entry in snapshot review inventory: {relative_path}"
            )
        if path.is_file():
            result.add(relative_path)
    return result


def snapshot_review_procedure_bytes() -> bytes:
    if set(SNAPSHOT_REVIEW_ACCEPTANCE_REQUIREMENTS) != set(EXTERNAL_REVIEW_HOOKS):
        raise IntegrationError("snapshot review acceptance requirement set is incomplete")
    lines = [
        "# V5 independent snapshot review procedure",
        "",
        "Review only a private copy produced by `integrate.py review-subject SNAPSHOT --private-copy PRIVATE_COPY`. Run `integrate.py review-custody-check --snapshot SNAPSHOT --private-copy PRIVATE_COPY` before inspecting semantic content. Run these commands from a separately trusted harness whose full Python/schema tool inventory equals the contract's reviewer-tool set; run `integrate.py reviewer-runtime-attestation` with that same interpreter to inspect the runtime identity which the receipt builder will bind. Read the hook-specific contract, verify every listed artifact and every acceptance requirement below, and authenticate the reviewer identity independently of the receipt bytes.",
        "",
        "Produce no receipt when any artifact, requirement, evidence item, or custody check is missing, unresolved, ambiguous, or failed. Otherwise author only the itemized work-product JSON and result JSON with the contract's exact ordered check IDs. The HOOK-SEMANTICS-CHECKED evidence must name the hook and the contract's acceptance-requirement SHA-256; a bare PASS assertion is invalid. Run `integrate.py build-snapshot-review-receipt --snapshot SNAPSHOT --private-copy PRIVATE_COPY --hook-id HOOK_ID --actor-id ACTOR_ID --work-product WORK_PRODUCT.json --result RESULT.json --output RECEIPTS/HOOK_ID.json`. The builder reruns custody, records the actual runtime, fills only deterministic contract/digest fields, validates the reviewer-authored work, reruns custody at the end, and no-replace-publishes canonical read-only JSON. After all eight actors finish, the coordinator must run `integrate.py validate-snapshot-review-receipts --snapshot SNAPSHOT --receipts RECEIPTS`.",
        "",
    ]
    for hook_id in sorted(SNAPSHOT_REVIEW_ACCEPTANCE_REQUIREMENTS):
        lines.extend((f"## {hook_id}", ""))
        for requirement in SNAPSHOT_REVIEW_ACCEPTANCE_REQUIREMENTS[hook_id]:
            lines.append(f"- {requirement}")
        lines.append("")
    return ("\n".join(lines).rstrip() + "\n").encode("utf-8")


def install_snapshot_review_procedure(root: Path) -> None:
    write_exclusive(
        root / SNAPSHOT_REVIEW_PROCEDURE_PATH,
        snapshot_review_procedure_bytes(),
    )


def derive_snapshot_review_contracts(root: Path) -> dict[str, dict[str, Any]]:
    """Bind each external review hook to an exact, complete artifact set."""

    procedure_path = root / SNAPSHOT_REVIEW_PROCEDURE_PATH
    procedure_bytes = snapshot_review_procedure_bytes()
    if (
        procedure_path.is_symlink()
        or not procedure_path.is_file()
        or procedure_path.read_bytes() != procedure_bytes
    ):
        raise IntegrationError("snapshot review procedure bytes are not exact")
    inventory = reviewable_snapshot_files(root)
    reviewer_tools = source_review_tool_records(RUN)
    reviewer_tool_set_sha256 = source_review_tool_set_sha256(reviewer_tools)
    selectors: dict[str, tuple[str, ...]] = {
        "H-VALIDATE-HIDDEN-FIXTURE-MANIFESTS": (
            "freeze/fixtures/",
            "freeze/controls",
            "static/integration/reviewed-inputs/reviewed-static/freeze/fixtures/",
            "static/integration/reviewed-static-input/freeze/fixtures/",
            "static/materialized/targets/",
            "targets.json",
        ),
        "H-VALIDATE-ORACLE-COVERAGE": (
            "freeze/oracle/",
            "freeze/atoms/",
            "freeze/allowlists/",
            "freeze/rules/",
            "freeze/authority/",
            "static/integration/reviewed-inputs/theorem-inputs/",
            "static/integration/source-declaration.json",
            "static/materialized/targets/",
            "targets.json",
        ),
        "H-VALIDATE-INDEPENDENT-SIGNOFFS": (
            "static/integration/reviewed-static-input/",
            "static/integration/reviewed-inputs/source-review-receipts/",
            "static/integration/reviewed-inputs/source-review-contracts/",
            "static/integration/reviewed-inputs/source-review-procedures/",
            "static/integration/reviewed-inputs/SOURCE-REVIEW.",
        ),
        "H-BUILD-VALIDATE-REPORT-AUTHORITY-PROJECTIONS": (
            "freeze/authority/",
            "static/materialized/common/docs/",
            "report-projection-contract.json",
            "schemas/agent-authority-packet.schema.json",
            "schemas/report-projection-",
        ),
        "H-VALIDATE-PROMPT-RENDERINGS": (
            "prompts/",
            "static/generated/report-prompts/",
            "static/generated/report-input-plans/",
            "static/generated/launch-records/",
            "static/generated/evaluator-prompts/",
            "static/generated/evaluator-launch-contracts.json",
            "static/generated/evaluator-prompt-validation-receipt.json",
            "static/generated/mode-launch-prompt-set.json",
            "static/generated/prompt-validation-receipt.json",
            "static/execution-manifests/",
            "static/envelope-specs/",
            "static/materialized/packages/",
            "packages.json",
        ),
        "H-GENERATE-VERIFY-RANDOMIZATION": (
            "randomization/",
            "static/generated/seeds.json",
            "static/generated/condition-map.json",
            "static/generated/target-map.json",
            "static/generated/blind-map.json",
            "static/generated/launch-schedule.json",
            "static/generated/presentation-orders.json",
            "static/generated/scoring-schedule.json",
            "static/generated/consistency-schedule.json",
            "static/generated/randomization-commitments.json",
            "static/generated/generation-binding.json",
        ),
        "H-VALIDATE-AGGREGATION-RULE-INVENTORY": (
            "aggregation-rules.json",
            "comparison-predicate.json",
            "gate-manifest.json",
            "materiality-review-contract.json",
            "root-inventory.json",
            "schemas/aggregate-",
            "schemas/aggregation-",
            "schemas/comparison-",
            "schemas/final-score.",
            "schemas/gate-",
            "schemas/materiality-",
        ),
        "H-VALIDATE-CROSS-REFERENCE-CLOSURE": (
            "integration-hooks.json",
            "runtime-policy.json",
            "plan.md",
            "integration.md",
            "prepare.py",
            "integrate.py",
            "protocol.py",
            "word_count.py",
            "static/integration/",
            "schemas/",
        ),
    }
    assigned: dict[str, set[str]] = {}
    for hook_id in sorted(EXTERNAL_REVIEW_HOOKS):
        prefixes = selectors[hook_id]
        assigned[hook_id] = {
            path
            for path in inventory
            if any(path == prefix or path.startswith(prefix) for prefix in prefixes)
        }
    # Cross-reference closure is the backstop which makes the union exhaustive;
    # no claimed pre-snapshot byte can escape all review contracts merely
    # because a new artifact was added under a previously unknown path.
    covered = set().union(*assigned.values())
    assigned["H-VALIDATE-CROSS-REFERENCE-CLOSURE"].update(inventory - covered)
    if set().union(*assigned.values()) != inventory:
        raise IntegrationError("snapshot review contracts do not cover every artifact")

    contracts: dict[str, dict[str, Any]] = {}
    for hook_id, paths in assigned.items():
        if not paths:
            raise IntegrationError(f"snapshot review contract is empty: {hook_id}")
        artifacts = [
            {"path": path, "sha256": sha256((root / path).read_bytes())}
            for path in sorted(paths)
        ]
        acceptance_requirements = list(
            SNAPSHOT_REVIEW_ACCEPTANCE_REQUIREMENTS[hook_id]
        )
        coverage_items = [
            {
                "id": f"artifact:{artifact['path']}",
                "subject": f"sha256={artifact['sha256']}",
            }
            for artifact in artifacts
        ] + [
            {
                "id": f"acceptance-requirement:{index:02d}",
                "subject": requirement,
            }
            for index, requirement in enumerate(acceptance_requirements, start=1)
        ]
        contract = {
            "schema_version": 1,
            "status": "READY",
            "hook_id": hook_id,
            "procedure_id": f"v5-snapshot-review/{hook_id.lower()}",
            "procedure_version": SNAPSHOT_REVIEW_PROCEDURE_VERSION,
            "procedure_path": SNAPSHOT_REVIEW_PROCEDURE_PATH,
            "procedure_sha256": sha256(procedure_bytes),
            "receipt_schema_path": SNAPSHOT_REVIEW_RECEIPT_SCHEMA_PATH,
            "receipt_schema_sha256": sha256(
                (root / SNAPSHOT_REVIEW_RECEIPT_SCHEMA_PATH).read_bytes()
            ),
            "reviewer_tool_set_algorithm": REVIEWER_TOOL_SET_ALGORITHM,
            "reviewer_tools": reviewer_tools,
            "reviewer_tool_set_sha256": reviewer_tool_set_sha256,
            "reviewer_runtime_attestation_algorithm": (
                REVIEWER_RUNTIME_ATTESTATION_ALGORITHM
            ),
            "custody_requirement": "VERIFIED_PRIVATE_COPY_AND_END_REVERIFY",
            "required_check_ids": list(SNAPSHOT_REVIEW_CHECK_IDS),
            "acceptance_requirements": acceptance_requirements,
            "acceptance_requirements_sha256": sha256(
                canonical_json_bytes(acceptance_requirements)
            ),
            "coverage_items": coverage_items,
            "coverage_set_algorithm": REVIEW_COVERAGE_SET_ALGORITHM,
            "coverage_set_sha256": review_coverage_set_sha256(coverage_items),
            "artifacts": artifacts,
            "artifact_set_sha256": sha256(canonical_json_bytes(artifacts)),
        }
        validate_schema_file(
            contract,
            RUN / "schemas" / "snapshot-review-contract.schema.json",
            f"snapshot review contract {hook_id}",
        )
        contracts[hook_id] = contract
    return contracts


def build_snapshot_review_contracts(root: Path) -> dict[str, dict[str, Any]]:
    contracts = derive_snapshot_review_contracts(root)
    contract_root = root / "static" / "integration" / "review-contracts"
    for hook_id, contract in contracts.items():
        write_json(contract_root / f"{hook_id}.json", contract)
    write_json(
        contract_root / "index.json",
        {
            "schema_version": 1,
            "status": "READY",
            "procedure_version": SNAPSHOT_REVIEW_PROCEDURE_VERSION,
            "contract_sha256": {
                hook_id: sha256(pretty_json_bytes(contract))
                for hook_id, contract in sorted(contracts.items())
            },
        },
    )
    return contracts


def validate_snapshot_review_contracts(root: Path) -> dict[str, dict[str, Any]]:
    contract_root = root / "static" / "integration" / "review-contracts"
    observed = {
        path.name for path in contract_root.iterdir() if path.is_file()
    } if contract_root.is_dir() else set()
    expected_names = {f"{hook_id}.json" for hook_id in EXTERNAL_REVIEW_HOOKS} | {
        "index.json"
    }
    if observed != expected_names or any(path.is_dir() for path in contract_root.rglob("*")):
        raise IntegrationError("snapshot review contract file inventory is not exact")
    expected = derive_snapshot_review_contracts(root)
    for hook_id, contract in expected.items():
        if read_json(contract_root / f"{hook_id}.json") != contract:
            raise IntegrationError(f"snapshot review contract drifted: {hook_id}")
    expected_index = {
        "schema_version": 1,
        "status": "READY",
        "procedure_version": SNAPSHOT_REVIEW_PROCEDURE_VERSION,
        "contract_sha256": {
            hook_id: sha256(pretty_json_bytes(contract))
            for hook_id, contract in sorted(expected.items())
        },
    }
    if read_json(contract_root / "index.json") != expected_index:
        raise IntegrationError("snapshot review contract index drifted")
    return expected


def validate_integration_receipt(
    value: Any,
    *,
    expected_hook_id: str,
    expected_phase: str,
    synthetic_capability: object | None = None,
) -> dict[str, Any]:
    """Validate the stable v2 receipt contract shared with ``protocol.py``."""

    expected_fields = {
        "schema_version",
        "status",
        "phase",
        "hook_id",
        "receipt_kind",
        "actor",
        "input_digests",
        "output_digests",
        "result",
    }
    if expected_phase == "SNAPSHOT_REVIEW":
        expected_fields.update({"reviewer_runtime", "work_product"})
    receipt = exact_object(
        value,
        expected_fields,
        f"receipt {expected_hook_id}",
    )
    if (
        receipt["schema_version"] != 2
        or receipt["status"]
        != (
            "SYNTHETIC-TEST-ONLY"
            if synthetic_capability is _SYNTHETIC_CAPABILITY
            else "PASS"
        )
        or receipt["phase"] != expected_phase
        or receipt["hook_id"] != expected_hook_id
        or HOOK_PHASES.get(expected_hook_id) != expected_phase
    ):
        raise IntegrationError(
            f"receipt does not pass the expected hook/phase: {expected_hook_id}"
        )
    expected_kind = (
        "INDEPENDENT_SNAPSHOT_REVIEW"
        if expected_phase == "SNAPSHOT_REVIEW"
        else "RUNTIME_VALIDATION"
        if expected_phase == "RUNTIME_COLLECTION"
        else "POSTRUN_VALIDATION"
    )
    if receipt["receipt_kind"] != expected_kind:
        raise IntegrationError(f"receipt kind is wrong for {expected_hook_id}")
    actor = exact_object(
        receipt["actor"],
        {"identity", "role", "implementation", "version"},
        f"receipt actor {expected_hook_id}",
    )
    if any(
        not isinstance(actor[field], str) or len(actor[field].strip()) < 2
        for field in actor
    ):
        raise IntegrationError(f"receipt actor is incomplete: {expected_hook_id}")
    if expected_phase == "SNAPSHOT_REVIEW" and actor["role"] != "INDEPENDENT_REVIEWER":
        raise IntegrationError(f"snapshot receipt actor is not an independent reviewer")
    if expected_phase == "SNAPSHOT_REVIEW":
        require_actor_id(actor["identity"], f"snapshot review actor {expected_hook_id}")
        validate_reviewer_runtime_attestation(receipt["reviewer_runtime"])
    for field in ("input_digests", "output_digests"):
        items = receipt[field]
        if not isinstance(items, dict) or not items or any(
            not isinstance(name, str)
            or not name
            or not isinstance(item, str)
            or not HEX64.fullmatch(item)
            for name, item in items.items()
        ):
            raise IntegrationError(f"receipt {expected_hook_id}.{field} is invalid")
    result = exact_object(
        receipt["result"], {"summary", "checks"}, f"receipt result {expected_hook_id}"
    )
    if not isinstance(result["summary"], str) or len(result["summary"].strip()) < 20:
        raise IntegrationError(f"receipt summary is not detailed: {expected_hook_id}")
    checks = result["checks"]
    if not isinstance(checks, list) or not checks:
        raise IntegrationError(f"receipt has no detailed checks: {expected_hook_id}")
    seen: set[str] = set()
    for check in checks:
        item = exact_object(
            check, {"id", "status", "evidence"}, f"receipt check {expected_hook_id}"
        )
        if (
            not isinstance(item["id"], str)
            or not re.fullmatch(r"[A-Z][A-Z0-9-]*", item["id"])
            or item["id"] in seen
            or item["status"] != "PASS"
            or not isinstance(item["evidence"], str)
            or len(item["evidence"].strip()) < 20
        ):
            raise IntegrationError(f"invalid detailed receipt check: {expected_hook_id}")
        seen.add(item["id"])
    validate_schema_file(
        receipt,
        RUN / "schemas" / "integration-receipt.schema.json",
        f"receipt {expected_hook_id}",
    )
    return receipt


def snapshot_receipt_inputs(
    root: Path,
    hook_id: str,
    *,
    reviewer_runtime: dict[str, Any],
) -> dict[str, str]:
    inputs = {
        SNAPSHOT_DESCRIPTOR: sha256((root / SNAPSHOT_DESCRIPTOR).read_bytes()),
        SNAPSHOT_MANIFEST: sha256((root / SNAPSHOT_MANIFEST).read_bytes()),
    }
    contract_path = f"static/integration/review-contracts/{hook_id}.json"
    inputs[contract_path] = sha256((root / contract_path).read_bytes())
    inputs[SNAPSHOT_REVIEW_PROCEDURE_PATH] = sha256(
        (root / SNAPSHOT_REVIEW_PROCEDURE_PATH).read_bytes()
    )
    inputs[SNAPSHOT_REVIEW_RECEIPT_SCHEMA_PATH] = sha256(
        (root / SNAPSHOT_REVIEW_RECEIPT_SCHEMA_PATH).read_bytes()
    )
    contract = read_json(
        root / f"static/integration/review-contracts/{hook_id}.json"
    )
    inputs["trusted-reviewer-tool-set"] = contract["reviewer_tool_set_sha256"]
    inputs["reviewer-runtime-attestation"] = sha256(
        canonical_json_bytes(reviewer_runtime)
    )
    return inputs


def _validate_snapshot_review_receipt_captured(
    path: Path,
    expected_hook: str,
    snapshot: Path,
    descriptor: dict[str, Any],
    *,
    synthetic_capability: object | None = None,
) -> tuple[dict[str, Any], bytes]:
    if synthetic_capability not in {None, _SYNTHETIC_CAPABILITY}:
        raise IntegrationError("unrecognized synthetic snapshot-review capability")
    raw_receipt, raw_bytes = capture_review_receipt_json(
        path,
        f"snapshot review receipt {expected_hook}",
        synthetic_capability=synthetic_capability,
    )
    receipt = validate_integration_receipt(
        raw_receipt,
        expected_hook_id=expected_hook,
        expected_phase="SNAPSHOT_REVIEW",
        synthetic_capability=synthetic_capability,
    )
    contract = validate_snapshot_review_contracts(snapshot)[expected_hook]
    reviewer_runtime = validate_reviewer_runtime_attestation(
        receipt["reviewer_runtime"]
    )
    if (
        reviewer_runtime["algorithm"]
        != contract["reviewer_runtime_attestation_algorithm"]
    ):
        raise IntegrationError("snapshot reviewer runtime algorithm drifted")
    _work_product, work_product_sha256 = validate_review_work_product(
        receipt["work_product"],
        expected_coverage_items=contract["coverage_items"],
    )
    if receipt["input_digests"] != snapshot_receipt_inputs(
        snapshot,
        expected_hook,
        reviewer_runtime=reviewer_runtime,
    ):
        raise IntegrationError(
            f"snapshot review does not bind the exact snapshot: {expected_hook}"
        )
    if receipt["output_digests"] != {
        "reviewed-payload-manifest": descriptor["payload_manifest_sha256"],
        "reviewed-artifact-set": contract["artifact_set_sha256"],
        "review-work-product": work_product_sha256,
    }:
        raise IntegrationError(
            f"snapshot review output does not identify the reviewed payload: {expected_hook}"
        )
    actor = receipt["actor"]
    if (
        actor["identity"].startswith("synthetic-")
        and synthetic_capability is not _SYNTHETIC_CAPABILITY
    ):
        raise IntegrationError("synthetic snapshot-review receipt cannot authorize production")
    if (
        actor["implementation"] != contract["procedure_id"]
        or actor["version"] != contract["procedure_version"]
    ):
        raise IntegrationError(
            f"snapshot reviewer did not use the locked procedure: {expected_hook}"
        )
    checks = receipt["result"]["checks"]
    if [check["id"] for check in checks] != contract["required_check_ids"]:
        raise IntegrationError(f"snapshot review check inventory is not exact: {expected_hook}")
    evidence = {check["id"]: check["evidence"] for check in checks}
    required_evidence = {
        "EXACT-SNAPSHOT-BOUND": (
            descriptor["payload_manifest_sha256"],
            receipt["input_digests"][SNAPSHOT_DESCRIPTOR],
        ),
        "REVIEW-CONTRACT-BOUND": (
            receipt["input_digests"][
                f"static/integration/review-contracts/{expected_hook}.json"
            ],
            contract["procedure_sha256"],
            contract["receipt_schema_sha256"],
            contract["procedure_version"],
            contract["coverage_set_algorithm"],
            contract["coverage_set_sha256"],
            contract["reviewer_tool_set_algorithm"],
            contract["reviewer_tool_set_sha256"],
            reviewer_runtime["algorithm"],
        ),
        "ARTIFACT-INVENTORY-CHECKED": (contract["artifact_set_sha256"],),
        "HOOK-SEMANTICS-CHECKED": (
            expected_hook,
            contract["acceptance_requirements_sha256"],
        ),
        "END-OF-REVIEW-REVERIFIED": (
            receipt["input_digests"][SNAPSHOT_MANIFEST],
            descriptor["payload_manifest_sha256"],
        ),
    }
    for check_id, needles in required_evidence.items():
        if any(needle not in evidence[check_id] for needle in needles):
            raise IntegrationError(
                f"snapshot review lacks exact evidence binding {expected_hook}.{check_id}"
            )
    return receipt, raw_bytes


def validate_snapshot_review_receipt(
    path: Path,
    expected_hook: str,
    snapshot: Path,
    descriptor: dict[str, Any],
    *,
    synthetic_capability: object | None = None,
) -> dict[str, Any]:
    receipt, _captured_bytes = _validate_snapshot_review_receipt_captured(
        path,
        expected_hook,
        snapshot,
        descriptor,
        synthetic_capability=synthetic_capability,
    )
    return receipt


SOURCE_COPY_ROOT_EXCLUSIONS = {
    STATIC_MANIFEST,
    STATIC_LOCK,
    "LOCK.json",
    "file-manifest.sha256",
    RUNTIME_ROOT,
}


def source_copy_excluded(relative_path: Path) -> bool:
    return (
        not relative_path.parts
        or relative_path.parts[0] in SOURCE_COPY_ROOT_EXCLUSIONS
        or "__pycache__" in relative_path.parts
        or any(part.startswith(".stage-") for part in relative_path.parts)
        or relative_path.suffix == ".pyc"
    )


def source_copy_ignore(directory: str, names: list[str]) -> set[str]:
    directory_path = Path(directory).resolve()
    try:
        relative_directory = directory_path.relative_to(RUN)
    except ValueError as error:
        raise IntegrationError(
            f"source-copy callback escaped the DRAFT run: {directory_path}"
        ) from error
    return {
        name
        for name in names
        if source_copy_excluded(relative_directory / name)
    }


def source_copy_manifest_bytes(root: Path) -> bytes:
    return tree_manifest_bytes(
        root,
        domain=b"ZEROCOPY\0V5\0SOURCE-COPY\0V1",
        excluded=source_copy_excluded,
        include_mode=False,
    )


def replace_snapshot_build_json(path: Path, value: Any) -> None:
    if path.is_symlink() or not path.is_file():
        raise IntegrationError(f"snapshot-build metadata is not a regular file: {path}")
    temporary = path.with_name(f".{path.name}.promote")
    write_exclusive(temporary, pretty_json_bytes(value))
    os.replace(temporary, path)
    fsync_directory(path.parent)


def replace_snapshot_build_bytes(path: Path, data: bytes) -> None:
    if path.is_symlink() or not path.is_file():
        raise IntegrationError(f"snapshot-build path is not a regular file: {path}")
    temporary = path.with_name(f".{path.name}.promote")
    write_exclusive(temporary, data)
    os.replace(temporary, path)
    fsync_directory(path.parent)


def promoted_schema_document(value: Any, name: str) -> dict[str, Any]:
    """Derive the one exact lifecycle promotion for a source schema."""

    if not isinstance(value, dict):
        raise IntegrationError(f"schema is not an object: {name}")
    comment = value.get("$comment")
    if not isinstance(comment, str) or not comment.strip():
        raise IntegrationError(f"schema lacks explicit lifecycle prose: {name}")
    promoted_comment = comment.replace(
        "DRAFT / UNSEALED", "READY / IMMUTABLE REVIEW-CANDIDATE"
    ).replace("DRAFT source", "trusted source")
    if "DRAFT" in promoted_comment or "UNSEALED" in promoted_comment:
        raise IntegrationError(
            f"schema comment contains an unrecognized source lifecycle marker: {name}"
        )
    return {**value, "$comment": promoted_comment}


def validate_promoted_schema_inventory(root: Path) -> None:
    """Require every staged schema to equal its trusted deterministic promotion."""

    source_root = RUN / "schemas"
    staged_root = root / "schemas"
    if staged_root.is_symlink() or not staged_root.is_dir():
        raise IntegrationError("promoted schema root must be a real directory")
    source_names = {
        path.name for path in source_root.iterdir() if path.is_file()
    }
    staged_names = {
        path.name for path in staged_root.iterdir() if path.is_file()
    }
    if staged_names != source_names or any(
        path.is_dir() or path.is_symlink() for path in staged_root.iterdir()
    ):
        raise IntegrationError("promoted schema inventory is not exact")
    for name in sorted(source_names):
        expected = promoted_schema_document(read_json(source_root / name), name)
        staged_path = staged_root / name
        if (
            read_json(staged_path) != expected
            or staged_path.read_bytes() != pretty_json_bytes(expected)
        ):
            raise IntegrationError(
                f"promoted schema does not equal trusted derivation: {name}"
            )


def promote_operational_metadata(stage: Path) -> None:
    hooks = validate_hook_inventory(stage, expected_status="DRAFT")
    hooks = {**hooks, "status": "READY"}
    replace_snapshot_build_json(stage / "integration-hooks.json", hooks)
    runtime = validate_runtime_policy(stage, expected_status="DRAFT")
    runtime = {**runtime, "status": "READY"}
    replace_snapshot_build_json(stage / "runtime-policy.json", runtime)
    promoted_contracts = {
        "gate-manifest.json": {"manifest_version": "v5-diagnostic-prequalification-1"},
        "root-inventory.json": {"inventory_version": "v5-diagnostic-prequalification-1"},
        "aggregation-rules.json": {},
        "comparison-predicate.json": {},
        "report-projection-contract.json": {},
        "materiality-review-contract.json": {},
    }
    for name, replacements in promoted_contracts.items():
        path = stage / name
        value = read_json(path)
        if not isinstance(value, dict) or value.get("status") != "DRAFT":
            raise IntegrationError(f"operational contract is not a DRAFT source: {name}")
        replace_snapshot_build_json(path, {**value, "status": "READY", **replacements})
    for path in sorted((stage / "schemas").glob("*.json")):
        replace_snapshot_build_json(
            path, promoted_schema_document(read_json(path), path.name)
        )
    markdown_paths = [stage / "plan.md", stage / "integration.md"]
    markdown_paths.extend(sorted((stage / "prompts").glob("*.md")))
    markdown_paths.extend(sorted((stage / "policies").glob("*.md")))
    for path in markdown_paths:
        data = path.read_bytes()
        if path.name == "plan.md":
            source_block = (
                b"> **Status: DRAFT / UNSEALED.** This directory is harness source, not a frozen\n"
                b"> evaluation. It intentionally contains no static lock, static file manifest,\n"
                b"> random seeds, generated maps, event ledger, target/package identities, completed report,\n"
                b"> score, or result. Any DRAFT atom/oracle/authority/allowlist/rule material\n"
                b"> under `freeze/` is unapproved integration input, not a frozen artifact.\n"
            )
            integrated_block = (
                b"> **Integrated status: REVIEW-CANDIDATE; launch requires a verified PRODUCTION STATIC-LOCK.**\n"
                b"> This is the reviewed-payload copy of the harness. Its final bundle kind, receipts,\n"
                b"> framed whole-tree manifest, and launch permission are authoritative only after\n"
                b"> successful finalization and trusted `verify-static` recomputation.\n"
            )
            if data.count(source_block) != 1:
                raise IntegrationError("plan source-status block is not exactly promotable")
            replace_snapshot_build_bytes(path, data.replace(source_block, integrated_block, 1))
            continue
        markers = (b" \xe2\x80\x94 DRAFT / UNSEALED\n", b"**Status: DRAFT / UNSEALED.**")
        found = sum(data.count(marker) for marker in markers)
        if found == 0 and path.name in {"report-controlled.md", "report-naturalistic.md"}:
            continue
        if found != 1:
            raise IntegrationError(
                f"operational document does not have one promotable DRAFT marker: {path}"
            )
        if markers[0] in data:
            data = data.replace(
                markers[0], b" \xe2\x80\x94 READY / STATIC-LOCK REQUIRED\n", 1
            )
        else:
            raise IntegrationError(f"unexpected prose status marker outside plan: {path}")
        replace_snapshot_build_bytes(path, data)
    validate_hook_inventory(stage, expected_status="READY")
    validate_runtime_policy(stage, expected_status="READY")
    validate_promoted_schema_inventory(stage)


def overlay_tree(source: Path, destination: Path) -> None:
    reject_unsupported_tree(source, "reviewed static overlay")
    for item in sorted(source.rglob("*"), key=lambda path: path.relative_to(source).as_posix()):
        relative_path = item.relative_to(source)
        target = destination / relative_path
        if item.is_dir():
            target.mkdir(parents=True, exist_ok=True)
        else:
            if relative_path.parts[0] in {RUNTIME_ROOT, STATIC_MANIFEST, STATIC_LOCK}:
                raise IntegrationError(f"reviewed overlay enters a reserved path: {relative_path}")
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(item, target)


def scan_tree_leakage(
    root: Path, forbidden_tokens: Iterable[str], *, label: str
) -> None:
    tokens = tuple(token.encode("utf-8") for token in forbidden_tokens)
    for path in sorted(root.rglob("*")):
        relative_text = path.relative_to(root).as_posix()
        relative_path = prepare.portable_relative_path(
            relative_text, f"agent-visible {label} entry"
        ).lower()
        data = path.read_bytes().lower() if path.is_file() else b""
        for token in tokens:
            if token in relative_path or token in data:
                raise IntegrationError(
                    f"{label} leakage scan found forbidden token {token.decode()!r} in {path}"
                )


def scan_target_leakage(root: Path, forbidden_tokens: Iterable[str]) -> None:
    scan_tree_leakage(
        root,
        sorted(set(forbidden_tokens) | set(PACKAGE_CROSS_CONDITION_FORBIDDEN_TOKENS)),
        label="target",
    )


def scan_package_cross_condition_leakage(
    root: Path,
    *,
    role: str,
    packages: dict[str, Any],
) -> None:
    """Scan treatment packages only for cross-condition/evaluator secrets.

    A package is intentionally treatment-bearing and may naturally say
    "package", "skill", or its own version name.  It must not identify the
    alternate package by content address or expose the no-skill/evaluator map.
    """

    alternate = "v4" if role == "v5" else "v5"
    alternate_record = packages.get(alternate)
    alternate_digest = (
        alternate_record.get("byte_tree_sha256")
        if isinstance(alternate_record, dict)
        else None
    )
    tokens = set(PACKAGE_CROSS_CONDITION_FORBIDDEN_TOKENS)
    if isinstance(alternate_digest, str):
        tokens.add(alternate_digest)
    scan_tree_leakage(root, sorted(tokens), label=f"{role} package")


def scan_agent_visible_file_leakage(
    path: Path, agent_visible_path: str, forbidden_tokens: Iterable[str]
) -> None:
    path_bytes = agent_visible_path.lower().encode("utf-8")
    data = path.read_bytes().lower()
    tokens = sorted(
        set(forbidden_tokens) | set(PACKAGE_CROSS_CONDITION_FORBIDDEN_TOKENS)
    )
    for token_text in tokens:
        token = token_text.encode("utf-8")
        if token in path_bytes or token in data:
            raise IntegrationError(
                f"agent-visible file leakage scan found forbidden token {token_text!r}: "
                f"{agent_visible_path}"
            )


def materialize_identities(
    stage: Path,
    source_root: Path,
    declaration: dict[str, Any],
    reviewed: dict[str, Any],
    inputs: Path,
) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    packages: dict[str, Any] = {"no_skill": None}
    source_bindings: dict[str, Any] = {"packages": {}, "targets": {}}
    for role in ("v5", "v4"):
        source_record = declaration["packages"][role]
        source_path = source_root / source_record["source_path"]
        reject_unsupported_tree(source_path, f"{role} package")
        tree_sha = prepare.byte_tree_v1(source_path)
        if source_record["directory_name_is_byte_tree_sha256"] and source_path.name != tree_sha:
            raise IntegrationError(
                f"{role} package directory name does not equal historical BYTE_TREE_V1: "
                f"{source_path.name} != {tree_sha}"
            )
        skill_path = source_path / source_record["skill_path"]
        if skill_path.is_symlink() or not skill_path.is_file():
            raise IntegrationError(f"{role} package has no real declared SKILL.md")
        skill_sha = sha256(skill_path.read_bytes())
        destination_relative = f"static/materialized/packages/{tree_sha}"
        copy_tree(source_path, stage / destination_relative)
        if prepare.byte_tree_v1(stage / destination_relative) != tree_sha:
            raise IntegrationError(f"materialized {role} package identity changed during copy")
        packages[role] = {
            "source_path": destination_relative,
            "byte_tree_sha256": tree_sha,
            "skill_sha256": skill_sha,
        }
        source_bindings["packages"][role] = {
            "declared_source_path": source_record["source_path"],
            "materialized_source_path": destination_relative,
            "byte_tree_sha256": tree_sha,
            "skill_sha256": skill_sha,
        }

    for role in ("v5", "v4"):
        package = packages[role]
        assert isinstance(package, dict)
        scan_package_cross_condition_leakage(
            stage / package["source_path"], role=role, packages=packages
        )

    authority_source_relative = relative(
        reviewed["authority_packet_path"], "authority packet path"
    )
    authority_source = inputs / authority_source_relative
    if authority_source.is_symlink() or not authority_source.is_file():
        raise IntegrationError("reviewed authority packet is not a regular file")
    authority_bytes = authority_source.read_bytes()
    parse_json_bytes(authority_bytes, str(authority_source))
    scan_agent_visible_file_leakage(
        authority_source,
        "docs/rust-documentation.json",
        reviewed["forbidden_tokens"],
    )
    authority_sha = sha256(authority_bytes)
    authority_relative = "static/materialized/common/docs/rust-documentation.json"
    write_exclusive(stage / authority_relative, authority_bytes)

    declared_targets = {item["mode"]: item for item in declaration["targets"]}
    targets: dict[str, dict[str, Any]] = {}
    for mode in prepare.MODES:
        source_record = declared_targets[mode]
        source_path = source_root / source_record["source_path"]
        reject_unsupported_tree(source_path, f"{mode} target")
        tree_sha = prepare.byte_tree_v1(source_path)
        scan_target_leakage(source_path, reviewed["forbidden_tokens"])
        destination_relative = f"static/materialized/targets/{mode.lower()}-{tree_sha}"
        copy_tree(source_path, stage / destination_relative)
        if prepare.byte_tree_v1(stage / destination_relative) != tree_sha:
            raise IntegrationError(f"materialized {mode} target identity changed during copy")
        parameters = reviewed["target_parameters"][mode]
        targets[mode] = {
            "mode": mode,
            "fixture_id": source_record["fixture_id"],
            "task_mode": parameters["task_mode"],
            "prompt_regime": source_record["prompt_regime"],
            "source_path": destination_relative,
            "byte_tree_sha256": tree_sha,
            "authority_packet_path": "docs/rust-documentation.json",
            "authority_packet_sha256": authority_sha,
            "authority_packet_visibility": "AGENT_VISIBLE_NEUTRAL",
            "word_cap": parameters["word_cap"],
        }
        source_bindings["targets"][mode] = {
            "fixture_id": source_record["fixture_id"],
            "provenance": source_record["provenance"],
            "declared_source_path": source_record["source_path"],
            "materialized_source_path": destination_relative,
            "byte_tree_sha256": tree_sha,
        }
    packages_document = {
        "schema_version": 1,
        "status": "READY",
        "packages": packages,
    }
    targets_document = {
        "schema_version": 1,
        "status": "READY",
        "targets": [targets[mode] for mode in prepare.MODES],
    }
    prepare.validate_packages(packages_document)
    prepare.validate_targets(targets_document)
    bindings_document = {
        "schema_version": 1,
        "status": "READY",
        "byte_tree_algorithm": prepare.BYTE_TREE_ALGORITHM,
        "source_declaration_sha256": reviewed["source_declaration_sha256"],
        "authority_packet_source_path": authority_source_relative,
        "authority_packet_materialized_path": authority_relative,
        "authority_packet_sha256": authority_sha,
        **source_bindings,
    }
    return packages_document, targets_document, bindings_document


def envelope_spec(output_path: str, max_bytes: int) -> dict[str, Any]:
    return {
        "schema_version": 1,
        "status": "READY",
        "files": [
            {"path": output_path, "required": True, "max_bytes": max_bytes, "utf8": True}
        ],
        "final_response": {
            "required": True,
            "max_bytes": 512,
            "utf8": True,
            "utf8_fullmatch_regex": re.escape(output_path) + r"\n?",
        },
        "max_total_output_bytes": max_bytes,
        "allowed_process_dispositions": ["RETURNED"],
    }


def build_execution_and_envelope_specs(
    stage: Path, reviewed: dict[str, Any]
) -> tuple[dict[str, str], dict[str, str]]:
    execution_digests: dict[str, str] = {}
    for role in ROLE_NAMES:
        manifest = {
            "schema_version": 1,
            "status": "READY",
            "role": role,
            "comparator_parity": "ONE_ROLE_MANIFEST_SHARED_ACROSS_ALL_CONDITIONS",
            **reviewed["execution_environment"][role],
        }
        data = pretty_json_bytes(manifest)
        write_exclusive(stage / "static" / "execution-manifests" / f"{role}.json", data)
        execution_digests[role] = sha256(data)

    spec_digests: dict[str, str] = {}
    for mode in prepare.MODES:
        cap = reviewed["target_parameters"][mode]["word_cap"]
        spec = envelope_spec("report.md", max(4096, cap * 16))
        data = pretty_json_bytes(spec)
        name = f"report-{mode}.json"
        write_exclusive(stage / "static" / "envelope-specs" / name, data)
        spec_digests[f"report-{mode}"] = sha256(data)
    role_outputs = {
        "scorer": "score.json",
        "consistency": "consistency.json",
        "adjudicator": "adjudication.json",
        "materiality-reviewer": "materiality-review.json",
        "materiality-adjudicator": "materiality-adjudication.json",
    }
    for role, output in role_outputs.items():
        data = pretty_json_bytes(envelope_spec(output, 4 * 1024 * 1024))
        write_exclusive(stage / "static" / "envelope-specs" / f"{role}.json", data)
        spec_digests[role] = sha256(data)
    write_json(
        stage / "static" / "envelope-specs" / "index.json",
        {
            "schema_version": 1,
            "status": "READY",
            "spec_sha256": spec_digests,
        },
    )
    return execution_digests, spec_digests


def render_evaluator_template(
    template: bytes, replacements: dict[str, str], *, label: str
) -> bytes:
    try:
        text = template.decode("utf-8", errors="strict")
    except UnicodeDecodeError as error:
        raise IntegrationError(f"evaluator template is not UTF-8: {label}") from error
    observed = set(re.findall(r"\{\{[A-Z0-9_]+\}\}", text))
    expected = {f"{{{{{name}}}}}" for name in replacements}
    if observed != expected or any(text.count(marker) != 1 for marker in expected):
        raise IntegrationError(
            f"evaluator template marker contract drifted: {label}; "
            f"observed={sorted(observed)}, expected={sorted(expected)}"
        )
    for name, value in replacements.items():
        if not isinstance(value, str) or not value or "\0" in value:
            raise IntegrationError(f"invalid evaluator prompt replacement {label}.{name}")
        text = text.replace(f"{{{{{name}}}}}", value, 1)
    if "{{" in text or "}}" in text:
        raise IntegrationError(f"unresolved evaluator prompt marker: {label}")
    return text.encode("utf-8")


def derive_evaluator_material(
    stage: Path,
    documents: dict[str, Any],
    execution_digests: dict[str, str],
    spec_digests: dict[str, str],
) -> tuple[dict[str, Any], dict[str, bytes]]:
    """Derive every possible evaluator prompt and runtime launch contract."""

    role_contracts = {
        "scorer": {
            "template": "prompts/scorer.md",
            "input_schema": "schemas/score-input-packet.schema.json",
            "output_schema": "schemas/score.schema.json",
            "output": "score.json",
        },
        "consistency": {
            "template": "prompts/consistency.md",
            "input_schema": "schemas/consistency-input-packet.schema.json",
            "output_schema": "schemas/consistency.schema.json",
            "output": "consistency.json",
        },
        "adjudicator": {
            "template": "prompts/adjudicator.md",
            "input_schema": "schemas/adjudication-packet.schema.json",
            "output_schema": "schemas/adjudication.schema.json",
            "output": "adjudication.json",
        },
        "materiality-reviewer": {
            "template": "prompts/materiality-reviewer.md",
            "input_schema": "schemas/materiality-review-packet.schema.json",
            "output_schema": "schemas/materiality-review.schema.json",
            "output": "materiality-review.json",
        },
        "materiality-adjudicator": {
            "template": "prompts/materiality-adjudicator.md",
            "input_schema": "schemas/materiality-adjudication-packet.schema.json",
            "output_schema": "schemas/materiality-adjudication.schema.json",
            "output": "materiality-adjudication.json",
        },
    }
    assignments: list[tuple[str, str, str | None, str, str]] = []
    for claim in documents["scoring-schedule.json"]["claims"]:
        mode, reviewer = claim.split("-", 1)
        assignments.append((claim, "scorer", mode, reviewer, "ALWAYS"))
    for claim in documents["consistency-schedule.json"]["claims"]:
        mode, reviewer = claim.split("-", 1)
        assignments.append((claim, "consistency", mode, reviewer, "ALWAYS"))
    assignments.extend(
        (f"{mode}-a1", "adjudicator", mode, "a1", "IF_INPUT_PACKET_NONEMPTY")
        for mode in prepare.MODES
    )
    assignments.extend(
        (
            ("m1", "materiality-reviewer", None, "m1", "ALWAYS"),
            ("m2", "materiality-reviewer", None, "m2", "ALWAYS"),
            (
                "ma1",
                "materiality-adjudicator",
                None,
                "ma1",
                "IF_INPUT_PACKET_NONEMPTY",
            ),
        )
    )
    if len(assignments) != 43 or len({item[0] for item in assignments}) != 43:
        raise IntegrationError("evaluator assignment inventory is not exactly 43 unique IDs")

    prompt_bytes: dict[str, bytes] = {}
    records: list[dict[str, Any]] = []
    for assignment_id, role, mode, reviewer_id, launch_condition in assignments:
        role_contract = role_contracts[role]
        template_path = role_contract["template"]
        template_file = stage / template_path
        if template_file.is_symlink() or not template_file.is_file():
            raise IntegrationError(f"evaluator prompt template is missing: {template_path}")
        template = template_file.read_bytes()
        if role == "scorer":
            replacements = {
                "MODE": str(mode),
                "SCORER_ID": reviewer_id,
                "INPUT_PACKET_PATH": "packet.json",
                "SCORE_SCHEMA_PATH": role_contract["output_schema"],
                "OUTPUT_PATH": role_contract["output"],
            }
        elif role == "consistency":
            replacements = {
                "REVIEWER_ID": reviewer_id,
                "INPUT_PACKET_PATH": "packet.json",
                "CONSISTENCY_SCHEMA_PATH": role_contract["output_schema"],
                "OUTPUT_PATH": role_contract["output"],
            }
        elif role == "adjudicator":
            replacements = {
                "INPUT_PACKET_PATH": "packet.json",
                "ADJUDICATION_SCHEMA_PATH": role_contract["output_schema"],
                "OUTPUT_PATH": role_contract["output"],
            }
        elif role == "materiality-reviewer":
            replacements = {
                "REVIEWER_ID": reviewer_id,
                "INPUT_PACKET_PATH": "packet.json",
                "REVIEW_SCHEMA_PATH": role_contract["output_schema"],
                "OUTPUT_PATH": role_contract["output"],
            }
        else:
            replacements = {
                "INPUT_PACKET_PATH": "packet.json",
                "ADJUDICATION_SCHEMA_PATH": role_contract["output_schema"],
                "OUTPUT_PATH": role_contract["output"],
            }
        rendered = render_evaluator_template(
            template, replacements, label=assignment_id
        )
        prompt_path = f"static/generated/evaluator-prompts/{assignment_id}.md"
        prompt_bytes[prompt_path] = rendered
        execution_path = f"static/execution-manifests/{role}.json"
        envelope_path = f"static/envelope-specs/{role}.json"
        record = {
            "assignment_id": assignment_id,
            "role": role,
            "mode": mode,
            "reviewer_id": reviewer_id,
            "launch_condition": launch_condition,
            "prompt_path": prompt_path,
            "prompt_sha256": sha256(rendered),
            "template_path": template_path,
            "template_sha256": sha256(template),
            "input_packet_path": "packet.json",
            "input_packet_schema_path": role_contract["input_schema"],
            "output_path": role_contract["output"],
            "output_schema_path": role_contract["output_schema"],
            "schema_paths": [role_contract["output_schema"]],
            "execution_manifest_path": execution_path,
            "execution_manifest_sha256": execution_digests[role],
            "envelope_spec_path": envelope_path,
            "envelope_spec_sha256": spec_digests[role],
        }
        records.append(record)
    contract = {
        "schema_version": 1,
        "status": "READY",
        "contract_id": "v5-evaluator-runtime-instantiation-v2",
        "packet_authority": "PROTOCOL_DERIVED_IMMUTABLE_AGGREGATION_STAGE",
        "production_lease_route": "ASSIGNMENT_ID_ONLY",
        "input_alias": "input",
        "output_alias": "output",
        "input_packet_path": "packet.json",
        "assignments": records,
    }
    validate_schema_file(
        contract,
        RUN / "schemas" / "evaluator-launch-contracts.schema.json",
        "evaluator-launch-contracts.json",
    )
    return contract, prompt_bytes


def build_evaluator_material(
    stage: Path,
    documents: dict[str, Any],
    execution_digests: dict[str, str],
    spec_digests: dict[str, str],
) -> dict[str, Any]:
    contract, prompts = derive_evaluator_material(
        stage, documents, execution_digests, spec_digests
    )
    for path_text, data in prompts.items():
        write_exclusive(stage / path_text, data)
    write_json(
        stage / "static" / "generated" / "evaluator-launch-contracts.json",
        contract,
    )
    write_json(
        stage / "static" / "generated" / "evaluator-prompt-validation-receipt.json",
        {
            "schema_version": 1,
            "status": "PASS",
            "contract_id": contract["contract_id"],
            "assignment_count": len(contract["assignments"]),
            "assignment_prompt_sha256": {
                record["assignment_id"]: record["prompt_sha256"]
                for record in contract["assignments"]
            },
            "unresolved_marker_count": 0,
        },
    )
    return contract


def prompt_without_invocation(data: bytes, invocation: str) -> bytes:
    encoded = invocation.encode("utf-8")
    if not encoded:
        return data
    if data.count(encoded) != 1:
        raise IntegrationError("rendered treatment prompt does not contain its invocation once")
    return data.replace(encoded, b"", 1)


def validate_agent_visible_mounts(
    root: Path,
    plan: dict[str, Any],
    *,
    condition_role: str,
    packages: dict[str, Any],
    target: dict[str, Any],
    forbidden_tokens: Iterable[str],
) -> None:
    """Recompute and leakage-scan the exact mounts for one scheduled report."""

    entries = plan.get("entries")
    if not isinstance(entries, list) or entries != sorted(
        entries, key=lambda item: item.get("destination", "") if isinstance(item, dict) else ""
    ):
        raise IntegrationError("report input-plan entries are not deterministically sorted")
    expected_entries = [
        {
            "destination": "input/target",
            "kind": "BYTE_TREE_V1_DIRECTORY",
            "source_path": target["source_path"],
            "sha256": target["byte_tree_sha256"],
        },
        {
            "destination": "input/docs/rust-documentation.json",
            "kind": "FILE",
            "source_path": "static/materialized/common/docs/rust-documentation.json",
            "sha256": target["authority_packet_sha256"],
        },
    ]
    package = packages[condition_role]
    if package is not None:
        expected_entries.append(
            {
                "destination": "input/package",
                "kind": "BYTE_TREE_V1_DIRECTORY",
                "source_path": package["source_path"],
                "sha256": package["byte_tree_sha256"],
            }
        )
    expected_entries.sort(key=lambda item: item["destination"])
    if entries != expected_entries:
        raise IntegrationError(
            "report input-plan does not equal the scheduled target and selected package mounts"
        )
    for raw in entries:
        entry = exact_object(
            raw, {"destination", "kind", "source_path", "sha256"}, "report mount"
        )
        source_path = root / relative(entry["source_path"], "report mount source")
        destination = entry["destination"]
        if destination == "input/target":
            if entry["kind"] != "BYTE_TREE_V1_DIRECTORY":
                raise IntegrationError("target mount is not a BYTE_TREE_V1 directory")
            if prepare.byte_tree_v1(source_path) != entry["sha256"]:
                raise IntegrationError("target mount digest changed")
            scan_target_leakage(source_path, forbidden_tokens)
        elif destination == "input/docs/rust-documentation.json":
            if entry["kind"] != "FILE" or sha256(source_path.read_bytes()) != entry["sha256"]:
                raise IntegrationError("authority mount digest changed")
            scan_agent_visible_file_leakage(
                source_path, "docs/rust-documentation.json", forbidden_tokens
            )
        elif destination == "input/package":
            if condition_role == "no_skill" or entry["kind"] != "BYTE_TREE_V1_DIRECTORY":
                raise IntegrationError("package mount is present for an invalid condition")
            if prepare.byte_tree_v1(source_path) != entry["sha256"]:
                raise IntegrationError("package mount digest changed")
            scan_package_cross_condition_leakage(
                source_path, role=condition_role, packages=packages
            )
        else:
            raise IntegrationError(f"unrecognized report-agent mount: {destination}")


def derive_report_material(
    stage: Path,
    documents: dict[str, Any],
    packages: dict[str, Any],
    targets: dict[str, dict[str, Any]],
    reviewed: dict[str, Any],
    workspace_base: Path,
    execution_digests: dict[str, str],
    spec_digests: dict[str, str],
) -> dict[str, Any]:
    """Derive every report-visible byte from authenticated static inputs."""

    conditions = {
        item["condition_label"]: item for item in documents["condition-map.json"]["conditions"]
    }
    target_rows = {
        item["target_label"]: item for item in documents["target-map.json"]["targets"]
    }
    schedule_bytes = pretty_json_bytes(documents["launch-schedule.json"])
    schedule_sha = sha256(schedule_bytes)
    prompt_records: dict[str, list[dict[str, str]]] = {mode: [] for mode in prepare.MODES}
    delta_groups: dict[tuple[str, int], dict[str, tuple[bytes, str]]] = {}
    launch_digests: dict[str, str] = {}
    prompts: dict[str, bytes] = {}
    input_plans: dict[str, bytes] = {}
    launches: dict[str, bytes] = {}
    for slot in documents["launch-schedule.json"]["slots"]:
        run_id = slot["run_id"]
        if not re.fullmatch(r"r(?!000)[0-9]{3}", run_id):
            raise IntegrationError(f"launch run ID is not padded r001..r120: {run_id}")
        target_row = target_rows[slot["target_label"]]
        mode = target_row["mode"]
        condition_row = conditions[slot["condition_label"]]
        role = condition_row["role"]
        invocation = reviewed["invocation_blocks"][role]
        prompt = prepare.render_report_prompt(
            target_row["prompt_regime"],
            invocation_block=invocation,
            input_root=prepare.INPUT_ALIAS,
            output_root=prepare.OUTPUT_ALIAS,
            target_path="target/REQUEST.md",
            authority_path="docs/rust-documentation.json",
            task_mode=target_row["task_mode"],
            output_path="report.md",
            word_cap=target_row["word_cap"],
        )
        neutral_prompt = prompt_without_invocation(prompt, invocation).lower()
        leaked = [
            token
            for token in sorted(
                set(reviewed["forbidden_tokens"])
                | set(PACKAGE_CROSS_CONDITION_FORBIDDEN_TOKENS)
            )
            if token.encode("utf-8") in neutral_prompt
        ]
        if leaked:
            raise IntegrationError(
                f"rendered prompt leaks forbidden tokens outside invocation block: {leaked}"
            )
        prompts[run_id] = prompt
        prompt_sha = sha256(prompt)
        prompt_records[mode].append(
            {"run_id": run_id, "cell_id": slot["cell_id"], "prompt_sha256": prompt_sha}
        )
        delta_groups.setdefault((mode, slot["replicate"]), {})[role] = (prompt, invocation)

        package = packages[role]
        # Reports emit Markdown.  Attempt envelopes are coordinator artifacts,
        # so exposing that schema to a report agent is both unnecessary and a
        # source of evaluator-context contamination.
        schema_paths: list[str] = []
        plan_entries = [
            {
                "destination": "input/target",
                "kind": "BYTE_TREE_V1_DIRECTORY",
                "source_path": target_row["source_path"],
                "sha256": target_row["byte_tree_sha256"],
            },
            {
                "destination": "input/docs/rust-documentation.json",
                "kind": "FILE",
                "source_path": "static/materialized/common/docs/rust-documentation.json",
                "sha256": target_row["authority_packet_sha256"],
            },
        ]
        if package is not None:
            plan_entries.append(
                {
                    "destination": "input/package",
                    "kind": "BYTE_TREE_V1_DIRECTORY",
                    "source_path": package["source_path"],
                    "sha256": package["byte_tree_sha256"],
                }
            )
        plan_entries.sort(key=lambda item: item["destination"])
        plan = {
            "schema_version": 1,
            "status": "READY",
            "run_id": run_id,
            "cell_id": slot["cell_id"],
            "input_alias": "input",
            "output_alias": "output",
            "entries": plan_entries,
        }
        validate_agent_visible_mounts(
            stage,
            plan,
            condition_role=role,
            packages=packages,
            target=target_row,
            forbidden_tokens=reviewed["forbidden_tokens"],
        )
        validate_schema_file(
            plan,
            RUN / "schemas" / "report-input-plan.schema.json",
            f"report input plan {run_id}",
        )
        plan_data = pretty_json_bytes(plan)
        input_plans[run_id] = plan_data
        workspace = workspace_base / slot["cell_id"]
        launch = {
            "schema_version": 1,
            "status": "READY",
            "role": "report",
            "assignment_id": run_id,
            "slot_id": run_id,
            "run_id": run_id,
            "cell_id": slot["cell_id"],
            "mode": mode,
            "fixture_id": target_row["fixture_id"],
            "task_mode": target_row["task_mode"],
            "prompt_regime": target_row["prompt_regime"],
            "condition_role": role,
            "condition_label": slot["condition_label"],
            "target_label": slot["target_label"],
            "replicate": slot["replicate"],
            "workspace_root": str(workspace),
            "input_root": str(workspace / "input"),
            "output_root": str(workspace / "output"),
            "target_path": "target/REQUEST.md",
            "output_path": "report.md",
            "schema_paths": sorted(schema_paths),
            "schedule_sha256": schedule_sha,
            "prompt_sha256": prompt_sha,
            "package_byte_tree_sha256": None if package is None else package["byte_tree_sha256"],
            "target_byte_tree_sha256": target_row["byte_tree_sha256"],
            "authority_packet_path": "docs/rust-documentation.json",
            "authority_packet_sha256": target_row["authority_packet_sha256"],
            "authority_packet_visibility": "AGENT_VISIBLE_NEUTRAL",
            "execution_manifest_sha256": execution_digests["report"],
            "input_packet_sha256": sha256(plan_data),
            "envelope_spec_sha256": spec_digests[f"report-{mode}"],
        }
        launch_data = pretty_json_bytes(launch)
        launches[run_id] = launch_data
        launch_digests[run_id] = sha256(launch_data)

    expected_ids = {f"r{index:03d}" for index in range(1, prepare.TOTAL_REPORTS + 1)}
    if set(launch_digests) != expected_ids:
        raise IntegrationError("rendered prompt/launch run-ID set is not exactly r001..r120")
    for key, group in delta_groups.items():
        if set(group) != set(prepare.CONDITIONS):
            raise IntegrationError(f"prompt delta group is incomplete: {key}")
        baselines = {
            role: prompt_without_invocation(prompt, invocation)
            for role, (prompt, invocation) in group.items()
        }
        if len(set(baselines.values())) != 1:
            raise IntegrationError(f"prompt bytes differ outside invocation block for {key}")
    prompt_set = {
        "schema_version": 1,
        "status": "READY",
        "modes": [
            {
                "mode": mode,
                "records": sorted(
                    prompt_records[mode], key=lambda item: int(item["run_id"][1:])
                ),
            }
            for mode in prepare.MODES
        ],
    }
    if any(len(item["records"]) != prepare.REPORTS_PER_MODE for item in prompt_set["modes"]):
        raise IntegrationError("mode prompt set does not contain exactly 15 records per mode")
    validation_receipt = {
        "schema_version": 1,
        "status": "PASS",
        "rendered_prompt_count": prepare.TOTAL_REPORTS,
        "run_ids": sorted(expected_ids, key=lambda item: int(item[1:])),
        "fixed_input_alias": "input",
        "fixed_output_alias": "output",
        "condition_delta": "INVOCATION_BLOCK_ONLY",
        "launch_record_sha256": launch_digests,
    }
    return {
        "prompts": prompts,
        "input_plans": input_plans,
        "launches": launches,
        "mode_launch_prompt_set": pretty_json_bytes(prompt_set),
        "prompt_validation_receipt": pretty_json_bytes(validation_receipt),
    }


def build_prompts_and_launches(
    stage: Path,
    documents: dict[str, Any],
    packages: dict[str, Any],
    targets: dict[str, dict[str, Any]],
    reviewed: dict[str, Any],
    workspace_base: Path,
    execution_digests: dict[str, str],
    spec_digests: dict[str, str],
) -> dict[str, Any]:
    material = derive_report_material(
        stage,
        documents,
        packages,
        targets,
        reviewed,
        workspace_base,
        execution_digests,
        spec_digests,
    )
    generated = stage / "static" / "generated"
    for run_id, data in material["prompts"].items():
        write_exclusive(generated / "report-prompts" / f"{run_id}.md", data)
    for run_id, data in material["input_plans"].items():
        write_exclusive(generated / "report-input-plans" / f"{run_id}.json", data)
    for run_id, data in material["launches"].items():
        write_exclusive(generated / "launch-records" / f"{run_id}.json", data)
    write_exclusive(
        generated / "mode-launch-prompt-set.json",
        material["mode_launch_prompt_set"],
    )
    write_exclusive(
        generated / "prompt-validation-receipt.json",
        material["prompt_validation_receipt"],
    )
    return material


def require_exact_flat_files(
    directory: Path, expected: dict[str, bytes], *, label: str
) -> None:
    if directory.is_symlink() or not directory.is_dir():
        raise IntegrationError(f"{label} root is not a real directory")
    if any(path.is_dir() for path in directory.rglob("*")):
        raise IntegrationError(f"{label} root contains an unexpected subdirectory")
    observed = {
        path.name: path.read_bytes()
        for path in directory.iterdir()
        if path.is_file() and not path.is_symlink()
    }
    if observed != expected or any(path.is_symlink() for path in directory.iterdir()):
        raise IntegrationError(f"{label} inventory or bytes are not the exact derivation")


def validate_report_material(
    root: Path,
    documents: dict[str, Any],
    packages: dict[str, Any],
    targets: dict[str, dict[str, Any]],
    reviewed: dict[str, Any],
    execution_digests: dict[str, str],
    spec_digests: dict[str, str],
) -> dict[str, Any]:
    """Rebuild and byte-compare every report prompt, launch, and input plan."""

    first_launch_path = root / "static" / "generated" / "launch-records" / "r001.json"
    first_launch = read_json(first_launch_path)
    workspace_root = first_launch.get("workspace_root") if isinstance(first_launch, dict) else None
    if not isinstance(workspace_root, str):
        raise IntegrationError("report launch does not bind a workspace root")
    candidate_workspace = Path(workspace_root)
    if (
        not candidate_workspace.is_absolute()
        or candidate_workspace.resolve() != candidate_workspace
        or candidate_workspace.name != first_launch.get("cell_id")
    ):
        raise IntegrationError("report launch workspace is not the exact cell path")
    workspace_base = require_neutral_workspace_base(
        candidate_workspace.parent,
        validate_runtime_policy(root, expected_status="READY")[
            "agent_visible_path_forbidden_terms"
        ],
    )
    expected = derive_report_material(
        root,
        documents,
        packages,
        targets,
        reviewed,
        workspace_base,
        execution_digests,
        spec_digests,
    )
    generated = root / "static" / "generated"
    require_exact_flat_files(
        generated / "report-prompts",
        {f"{run_id}.md": data for run_id, data in expected["prompts"].items()},
        label="report prompt",
    )
    require_exact_flat_files(
        generated / "report-input-plans",
        {f"{run_id}.json": data for run_id, data in expected["input_plans"].items()},
        label="report input-plan",
    )
    require_exact_flat_files(
        generated / "launch-records",
        {f"{run_id}.json": data for run_id, data in expected["launches"].items()},
        label="report launch-record",
    )
    for name, data in (
        ("mode-launch-prompt-set.json", expected["mode_launch_prompt_set"]),
        ("prompt-validation-receipt.json", expected["prompt_validation_receipt"]),
    ):
        path = generated / name
        if path.is_symlink() or not path.is_file() or path.read_bytes() != data:
            raise IntegrationError(f"{name} is not the exact report-material derivation")
    return expected


def mode_report_material_digests(
    material: dict[str, Any], documents: dict[str, Any]
) -> dict[str, str]:
    """Bind exact per-mode prompt, input-plan, and launch-record bytes."""

    records: dict[str, list[dict[str, Any]]] = {mode: [] for mode in prepare.MODES}
    mode_by_target_label = {
        row["target_label"]: row["mode"]
        for row in documents["target-map.json"]["targets"]
    }
    for slot in documents["launch-schedule.json"]["slots"]:
        try:
            mode = mode_by_target_label[slot["target_label"]]
        except KeyError as error:
            raise IntegrationError(
                "report-material binding schedule references an unknown target label"
            ) from error
        run_id = slot["run_id"]
        record: dict[str, Any] = {"run_id": run_id}
        for key, field in (
            ("prompts", "prompt"),
            ("input_plans", "input_plan"),
            ("launches", "launch_record"),
        ):
            data = material[key][run_id]
            record[f"{field}_length"] = len(data)
            record[f"{field}_sha256"] = sha256(data)
        records[mode].append(record)
    result: dict[str, str] = {}
    domain = REPORT_MATERIAL_SET_ALGORITHM.encode("ascii") + b"\0"
    for mode in prepare.MODES:
        ordered = sorted(records[mode], key=lambda item: int(item["run_id"][1:]))
        if len(ordered) != prepare.REPORTS_PER_MODE:
            raise IntegrationError(f"mode {mode} does not have exactly 15 report records")
        binding = {
            "schema_version": 1,
            "algorithm": REPORT_MATERIAL_SET_ALGORITHM,
            "mode": mode,
            "records": ordered,
        }
        result[mode] = sha256(domain + canonical_json_bytes(binding))
    return result


def derive_ready_fixture_bytes(
    reviewed_source_root: Path,
    *,
    source_digests: dict[str, str],
    material_digests: dict[str, str],
) -> dict[str, bytes]:
    if set(source_digests) != set(prepare.MODES) or set(material_digests) != set(prepare.MODES):
        raise IntegrationError("fixture binding maps must cover every mode")
    result: dict[str, bytes] = {}
    for mode in prepare.MODES:
        path_text = f"freeze/fixtures/{mode}.json"
        value = read_json(reviewed_source_root / path_text)
        if value.get("status") != REVIEWED_FIXTURE_STATUS:
            raise IntegrationError(f"fixture {mode} is not an honest reviewed-source input")
        if (
            value.get("source_tree_algorithm") != prepare.BYTE_TREE_ALGORITHM
            or value.get("source_tree_sha256") != source_digests[mode]
            or value.get("report_material_set_algorithm") != REPORT_MATERIAL_SET_ALGORITHM
            or value.get("exact_report_material_set_sha256")
            != REVIEWED_DERIVATION_SENTINEL
        ):
            raise IntegrationError(f"fixture {mode} reviewed-source bindings are invalid")
        value = {
            **value,
            "status": "READY",
            "exact_report_material_set_sha256": material_digests[mode],
        }
        validate_schema_file(
            value,
            RUN / "schemas" / "fixture-manifest.schema.json",
            f"derived READY fixture {mode}",
        )
        result[path_text] = pretty_json_bytes(value)
    return result


def install_ready_fixture_manifests(
    stage: Path,
    reviewed_source_root: Path,
    *,
    source_digests: dict[str, str],
    material_digests: dict[str, str],
) -> None:
    expected = derive_ready_fixture_bytes(
        reviewed_source_root,
        source_digests=source_digests,
        material_digests=material_digests,
    )
    for path_text, data in expected.items():
        replace_snapshot_build_bytes(stage / path_text, data)


def require_exact_ready_fixture_manifests(
    root: Path,
    reviewed_source_root: Path,
    *,
    source_digests: dict[str, str],
    material_digests: dict[str, str],
) -> None:
    expected = derive_ready_fixture_bytes(
        reviewed_source_root,
        source_digests=source_digests,
        material_digests=material_digests,
    )
    for path_text, data in expected.items():
        if (root / path_text).read_bytes() != data:
            raise IntegrationError(f"READY fixture is not the exact derived binding: {path_text}")


def validate_word_counter_bytes(source_bytes: bytes, source_label: str) -> dict[str, Any]:
    """Execute one already trusted word-counter byte object."""

    if not isinstance(source_bytes, bytes):
        raise IntegrationError("trusted word counter source must be bytes")
    module = types.ModuleType("_v5_exact_staged_word_counter")
    module.__file__ = source_label
    try:
        code = compile(source_bytes, source_label, "exec", dont_inherit=True)
        exec(code, module.__dict__)
    except Exception as error:
        raise IntegrationError("exact staged word-counter bytes failed to load") from error
    count_words = getattr(module, "count_words", None)
    algorithm_id = getattr(module, "ALGORITHM_ID", None)
    if not callable(count_words) or not isinstance(algorithm_id, str) or not algorithm_id:
        raise IntegrationError("exact staged word counter lacks its required API")
    cases = {
        b"": 0,
        b"one two\nthree": 3,
        "alpha\u00a0beta\tem dash—stays".encode("utf-8"): 4,
        "标识 符".encode("utf-8"): 2,
    }
    for data, expected in cases.items():
        if count_words(data) != expected:
            raise IntegrationError("frozen word counter failed its integration self-test")
    try:
        count_words(b"\xff")
    except UnicodeDecodeError:
        pass
    else:
        raise IntegrationError("frozen word counter accepted invalid UTF-8")
    return {
        "schema_version": 1,
        "status": "READY",
        "algorithm_id": algorithm_id,
        "source_path": "word_count.py",
        "source_sha256": sha256(source_bytes),
        "self_test": "PASS",
    }


def validate_word_counter(source_path: Path) -> dict[str, Any]:
    """Prove staged bytes equal trusted bytes and execute only the trusted capture."""

    staged_bytes = capture_regular_file_bytes(
        source_path, "staged word counter", require_read_only=False
    )
    trusted_path = RUN / "word_count.py"
    trusted_bytes = capture_regular_file_bytes(
        trusted_path, "trusted word counter", require_read_only=False
    )
    if staged_bytes != trusted_bytes:
        raise IntegrationError("staged word counter differs from trusted harness bytes")
    binding = validate_word_counter_bytes(trusted_bytes, str(trusted_path))
    if (
        capture_regular_file_bytes(
            source_path, "staged word counter recheck", require_read_only=False
        )
        != staged_bytes
    ):
        raise IntegrationError("staged word counter changed during validation")
    return binding


def copy_snapshot_review_receipts(
    stage: Path,
    snapshot: Path,
    receipts: Path,
    descriptor: dict[str, Any],
    *,
    synthetic_capability: object | None,
) -> dict[str, str]:
    reject_unsupported_tree(receipts, "snapshot review receipt root")
    observed = {
        path.relative_to(receipts).as_posix()
        for path in receipts.rglob("*")
        if path.is_file()
    }
    expected = {f"{hook_id}.json" for hook_id in EXTERNAL_REVIEW_HOOKS}
    if observed != expected:
        raise IntegrationError(
            "snapshot review receipt inventory is not exact; "
            f"missing={sorted(expected - observed)}, extra={sorted(observed - expected)}"
        )
    if any(path.is_dir() for path in receipts.rglob("*")):
        raise IntegrationError("snapshot review receipt root may not contain directories")
    result: dict[str, str] = {}
    snapshot_actor_ids: list[str] = []
    for hook_id in sorted(EXTERNAL_REVIEW_HOOKS):
        source = receipts / f"{hook_id}.json"
        validated_receipt, data = _validate_snapshot_review_receipt_captured(
            source,
            hook_id,
            snapshot,
            descriptor,
            synthetic_capability=synthetic_capability,
        )
        snapshot_actor_ids.append(validated_receipt["actor"]["identity"])
        destination = stage / "static" / "integration-receipts" / source.name
        write_exclusive(destination, data)
        result[hook_id] = sha256(data)
    if len(set(snapshot_actor_ids)) != len(EXTERNAL_REVIEW_HOOKS):
        raise IntegrationError("snapshot reviewer identities must be pairwise distinct")
    preserved_source_receipts = (
        snapshot
        / "static"
        / "integration"
        / "reviewed-inputs"
        / "source-review-receipts"
    )
    if preserved_source_receipts.is_dir():
        source_actor_ids = {
            read_json(preserved_source_receipts / name)["actor"]["identity"]
            for name, _review_kind in SOURCE_REVIEW_KINDS
        }
        if len(source_actor_ids) != len(SOURCE_REVIEW_KINDS):
            raise IntegrationError("source reviewer identities are not distinct")
        if source_actor_ids.intersection(snapshot_actor_ids):
            raise IntegrationError(
                "source and snapshot reviewer identities must be disjoint"
            )
    write_json(
        stage / "static" / "integration-receipts" / "index.json",
        {
            "schema_version": 2,
            "status": "READY",
            "phase": "SNAPSHOT_REVIEW",
            "snapshot_descriptor_sha256": sha256(
                (snapshot / SNAPSHOT_DESCRIPTOR).read_bytes()
            ),
            "snapshot_manifest_sha256": sha256(
                (snapshot / SNAPSHOT_MANIFEST).read_bytes()
            ),
            "receipt_sha256": result,
        },
    )
    return result


def locked_reviewer_actor_ids(
    *,
    captured_source_receipts: dict[str, dict[str, Any]],
    captured_snapshot_receipts: dict[str, dict[str, Any]],
) -> frozenset[str]:
    """Derive exclusions solely from receipts captured by one verification."""

    if set(captured_source_receipts) != {
        name for name, _kind in SOURCE_REVIEW_KINDS
    }:
        raise IntegrationError("captured source reviewer receipt set is not exact")
    if set(captured_snapshot_receipts) != EXTERNAL_REVIEW_HOOKS:
        raise IntegrationError("captured snapshot reviewer receipt set is not exact")
    identities = [
        require_actor_id(
            captured_source_receipts[name]["actor"]["identity"],
            f"locked source reviewer {name}",
        )
        for name, _kind in SOURCE_REVIEW_KINDS
    ] + [
        require_actor_id(
            captured_snapshot_receipts[hook_id]["actor"]["identity"],
            f"locked snapshot reviewer {hook_id}",
        )
        for hook_id in sorted(EXTERNAL_REVIEW_HOOKS)
    ]
    if len(identities) != 11 or len(set(identities)) != 11:
        raise IntegrationError("locked reviewer identity inventory is not eleven distinct actors")
    return frozenset(identities)


def validate_runtime_carve_out(root: Path) -> None:
    runtime = root / RUNTIME_ROOT
    if not runtime.exists():
        return
    if runtime.is_symlink() or not runtime.is_dir():
        raise IntegrationError("runtime carve-out root must be a real directory")
    children = list(runtime.iterdir())
    if any(child.name != "state" for child in children):
        raise IntegrationError("only runtime/state is excluded from the static manifest")
    state = runtime / "state"
    if state.exists():
        reject_unsupported_tree(state, "runtime/state")


def static_excluded(relative_path: Path) -> bool:
    return (
        relative_path.parts[:2] == ("runtime", "state")
        and len(relative_path.parts) > 2
    ) or relative_path.as_posix() in {STATIC_MANIFEST, STATIC_LOCK}


def snapshot_excluded(relative_path: Path) -> bool:
    text = relative_path.as_posix()
    return (
        relative_path.parts[:2] == ("runtime", "state")
        and len(relative_path.parts) > 2
    ) or text in {
        SNAPSHOT_MANIFEST,
        SNAPSHOT_DESCRIPTOR,
        STATIC_MANIFEST,
        STATIC_LOCK,
        "INTEGRATION-STATUS.json",
    } or relative_path.parts[:2] == ("static", "integration-receipts")


def count_tree_entries(root: Path, excluded: Callable[[Path], bool]) -> int:
    return sum(1 for path in root.rglob("*") if not excluded(path.relative_to(root)))


def reject_interpreter_artifacts(root: Path) -> None:
    for path in root.rglob("*"):
        relative_path = path.relative_to(root)
        if "__pycache__" in relative_path.parts or relative_path.suffix == ".pyc":
            raise IntegrationError(f"interpreter artifact in committed tree: {relative_path}")


def manifest_bytes(root: Path) -> bytes:
    validate_runtime_carve_out(root)
    reject_interpreter_artifacts(root)
    return tree_manifest_bytes(
        root,
        domain=b"ZEROCOPY\0V5\0STATIC-MANIFEST\0V1",
        excluded=static_excluded,
        include_mode=True,
    )


def snapshot_manifest_bytes(root: Path) -> bytes:
    reject_interpreter_artifacts(root)
    return tree_manifest_bytes(
        root,
        domain=b"ZEROCOPY\0V5\0REVIEW-SNAPSHOT\0V1",
        excluded=snapshot_excluded,
        include_mode=False,
    )


def source_review_excluded(relative_path: Path) -> bool:
    if not relative_path.parts:
        return False
    return relative_path.parts[0] in {
        SOURCE_REVIEW_MANIFEST,
        SOURCE_REVIEW_DESCRIPTOR,
        "source-review-receipts",
    }


def source_review_manifest_bytes(root: Path) -> bytes:
    reject_interpreter_artifacts(root)
    return tree_manifest_bytes(
        root,
        domain=b"ZEROCOPY\0V5\0SOURCE-REVIEW\0V1",
        excluded=source_review_excluded,
        include_mode=False,
    )


def normalize_read_only_review_tree(root: Path) -> None:
    for path in root.rglob("*"):
        os.chmod(path, 0o555 if path.is_dir() else 0o444, follow_symlinks=False)
    os.chmod(root, 0o555)


def verify_read_only_review_tree(root: Path) -> None:
    if stat.S_IMODE(root.stat().st_mode) != 0o555:
        raise IntegrationError("source-review root mode is not 0555")
    for path in root.rglob("*"):
        expected = 0o555 if path.is_dir() else 0o444
        if stat.S_IMODE(path.stat().st_mode) != expected:
            raise IntegrationError(f"source-review mode is not {expected:o}: {path}")


def fsync_tree(root: Path) -> None:
    reject_unsupported_tree(root, "fsync tree")
    for path in root.rglob("*"):
        if path.is_file():
            descriptor = os.open(path, os.O_RDONLY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
    directories = [root] + [path for path in root.rglob("*") if path.is_dir()]
    directories.sort(key=lambda path: len(path.parts), reverse=True)
    for directory in directories:
        fsync_directory(directory)


def make_tree_writable(root: Path) -> None:
    for path in root.rglob("*"):
        os.chmod(path, 0o750 if path.is_dir() else 0o640, follow_symlinks=False)
    os.chmod(root, 0o750)


def normalize_final_permissions(root: Path) -> None:
    runtime = root / RUNTIME_ROOT
    state = root / RUNTIME_STATE
    state.mkdir(parents=True, exist_ok=True)
    for path in root.rglob("*"):
        relative_path = path.relative_to(root)
        if relative_path.parts[:1] == (RUNTIME_ROOT,):
            if path in {runtime, state}:
                os.chmod(path, 0o700)
            continue
        os.chmod(path, 0o555 if path.is_dir() else 0o444, follow_symlinks=False)
    os.chmod(root, 0o555)


def verify_final_permissions(root: Path) -> None:
    if stat.S_IMODE(root.stat().st_mode) != 0o555:
        raise IntegrationError("static bundle root mode is not 0555")
    for path in root.rglob("*"):
        relative_path = path.relative_to(root)
        if relative_path.parts[:1] == (RUNTIME_ROOT,):
            if path in {root / RUNTIME_ROOT, root / RUNTIME_STATE} and stat.S_IMODE(
                path.stat().st_mode
            ) != 0o700:
                raise IntegrationError(f"runtime root mode is not 0700: {relative_path}")
            continue
        expected = 0o555 if path.is_dir() else 0o444
        if stat.S_IMODE(path.stat().st_mode) != expected:
            raise IntegrationError(
                f"static metadata mode mismatch for {relative_path}: expected {expected:o}"
            )


def create_review_snapshot(root: Path, *, bundle_kind: str) -> dict[str, Any]:
    if bundle_kind not in BUNDLE_KINDS:
        raise IntegrationError(f"unknown bundle kind: {bundle_kind!r}")
    forbidden = [
        relative.as_posix()
        for relative in (
            Path(SNAPSHOT_MANIFEST),
            Path(SNAPSHOT_DESCRIPTOR),
            Path(STATIC_MANIFEST),
            Path(STATIC_LOCK),
            Path("INTEGRATION-STATUS.json"),
            Path("static/integration-receipts"),
        )
        if (root / relative).exists()
    ]
    if forbidden:
        raise IntegrationError(f"snapshot stage contains finalization artifacts: {forbidden}")
    require_empty_runtime_state(root, "review snapshot creation")
    payload = snapshot_manifest_bytes(root)
    write_exclusive(root / SNAPSHOT_MANIFEST, payload)
    descriptor = {
        "schema_version": 1,
        "status": "REVIEW-CANDIDATE",
        "candidate_for_bundle_kind": bundle_kind,
        "payload_manifest_path": SNAPSHOT_MANIFEST,
        "payload_manifest_algorithm": MANIFEST_ALGORITHM,
        "payload_manifest_sha256": sha256(payload),
        "payload_entry_count": count_tree_entries(root, snapshot_excluded),
        "path_domain": PATH_DOMAIN,
        "finalization_additions": [
            "INTEGRATION-STATUS.json",
            "static/integration-receipts/**",
            STATIC_MANIFEST,
            STATIC_LOCK,
        ],
    }
    validate_schema_file(
        descriptor,
        RUN / "schemas" / "review-snapshot.schema.json",
        SNAPSHOT_DESCRIPTOR,
    )
    write_json(root / SNAPSHOT_DESCRIPTOR, descriptor)
    normalize_final_permissions(root)
    fsync_tree(root)
    return descriptor


def validate_snapshot_build_products(root: Path, *, bundle_kind: str) -> None:
    """Re-run the mechanical SNAPSHOT_BUILD obligations on staged bytes."""

    validate_promoted_schema_inventory(root)
    preserved_inputs = root / "static" / "integration" / "reviewed-inputs"
    reviewed_production_inputs = bundle_kind == "PRODUCTION" or preserved_inputs.is_dir()
    if bundle_kind == "PRODUCTION" and not preserved_inputs.is_dir():
        raise IntegrationError("PRODUCTION snapshot lacks finalized reviewed inputs")
    if reviewed_production_inputs:
        for name in ("integrate.py", "prepare.py", "protocol.py", "word_count.py"):
            if (root / name).read_bytes() != (RUN / name).read_bytes():
                raise IntegrationError(
                    f"PRODUCTION snapshot {name} differs from the trusted verifier bytes"
                )
    operational_contracts = {
        "gate-manifest.json": {
            "manifest_version": "v5-diagnostic-prequalification-1"
        },
        "root-inventory.json": {
            "inventory_version": "v5-diagnostic-prequalification-1"
        },
        "aggregation-rules.json": {},
        "comparison-predicate.json": {},
        "report-projection-contract.json": {},
        "materiality-review-contract.json": {},
    }
    for name, exact_fields in operational_contracts.items():
        value = read_json(root / name)
        if (
            not isinstance(value, dict)
            or value.get("status") != "READY"
            or any(value.get(key) != expected for key, expected in exact_fields.items())
        ):
            raise IntegrationError(
                f"promoted operational contract identity is not exact: {name}"
            )
    declaration_bytes = (root / "static" / "integration" / "source-declaration.json").read_bytes()
    if reviewed_production_inputs and declaration_bytes != trusted_production_declaration_bytes():
        raise IntegrationError(
            "PRODUCTION snapshot does not embed the exact trusted source declaration bytes"
        )
    declaration = validate_source_declaration(
        parse_json_bytes(declaration_bytes, "locked source declaration"),
        production=reviewed_production_inputs,
    )
    values_bytes = (root / "static" / "integration" / "integration-values.json").read_bytes()
    values = validate_reviewed_values(
        parse_json_bytes(values_bytes, "locked integration values"),
        declaration_bytes,
        expected_reviewed_static_base=REVIEWED_STATIC_BUNDLE_BASE,
    )
    reviewed_source_root = root / "static" / "integration" / "reviewed-static-input"
    if reviewed_production_inputs:
        verify_source_review_snapshot(
            preserved_inputs,
            require_receipts=True,
            require_read_only=False,
            synthetic_capability=(
                _SYNTHETIC_CAPABILITY
                if bundle_kind == "SYNTHETIC-TEST-ONLY"
                else None
            ),
        )
    validate_reviewed_static(reviewed_source_root, values["reviewed_static"])
    if reviewed_production_inputs:
        require_exact_ready_reviewed_source_files(root, reviewed_source_root)
    packages_document = read_json(root / "packages.json")
    targets_document = read_json(root / "targets.json")
    packages = prepare.validate_packages(packages_document)
    targets = prepare.validate_targets(targets_document)
    trusted_declaration = (
        validate_source_declaration(
            parse_json_bytes(
                trusted_production_declaration_bytes(),
                "trusted production source declaration",
            ),
            production=True,
        )
        if reviewed_production_inputs
        else declaration
    )
    for role in ("v5", "v4"):
        package = packages[role]
        if package is None:
            raise IntegrationError(f"materialized package unexpectedly absent: {role}")
        package_root = root / package["source_path"]
        if prepare.byte_tree_v1(package_root) != package["byte_tree_sha256"]:
            raise IntegrationError(f"materialized package tree changed: {role}")
        source_record = declaration["packages"][role]
        skill = package_root / source_record["skill_path"]
        if sha256(skill.read_bytes()) != package["skill_sha256"]:
            raise IntegrationError(f"materialized SKILL.md bytes changed: {role}")
        if reviewed_production_inputs:
            trusted_record = trusted_declaration["packages"][role]
            trusted_root, trusted_tree_sha = trusted_declared_tree(
                trusted_record["source_path"], f"{role} package"
            )
            trusted_skill = trusted_root / trusted_record["skill_path"]
            expected_materialized = f"static/materialized/packages/{trusted_tree_sha}"
            if (
                trusted_root.name != trusted_tree_sha
                or package["source_path"] != expected_materialized
                or package["byte_tree_sha256"] != trusted_tree_sha
                or package["skill_sha256"] != sha256(trusted_skill.read_bytes())
            ):
                raise IntegrationError(
                    f"PRODUCTION package identity is not the trusted declared package: {role}"
                )
        scan_package_cross_condition_leakage(
            package_root, role=role, packages=packages
        )
    authority = root / "static" / "materialized" / "common" / "docs" / "rust-documentation.json"
    parse_json_bytes(authority.read_bytes(), "materialized authority packet")
    for mode, target in targets.items():
        target_root = root / target["source_path"]
        if prepare.byte_tree_v1(target_root) != target["byte_tree_sha256"]:
            raise IntegrationError(f"materialized target tree changed: {mode}")
        scan_target_leakage(target_root, values["forbidden_tokens"])
        if sha256(authority.read_bytes()) != target["authority_packet_sha256"]:
            raise IntegrationError(f"materialized authority binding changed: {mode}")
        if reviewed_production_inputs:
            trusted_record = next(
                item for item in trusted_declaration["targets"] if item["mode"] == mode
            )
            _trusted_root, trusted_tree_sha = trusted_declared_tree(
                trusted_record["source_path"], f"{mode} target"
            )
            expected_materialized = (
                f"static/materialized/targets/{mode.lower()}-{trusted_tree_sha}"
            )
            if (
                target["source_path"] != expected_materialized
                or target["byte_tree_sha256"] != trusted_tree_sha
                or target["fixture_id"] != trusted_record["fixture_id"]
                or target["prompt_regime"] != trusted_record["prompt_regime"]
            ):
                raise IntegrationError(
                    f"PRODUCTION target identity is not the trusted declared target: {mode}"
                )
    expected_bindings = {
        "schema_version": 1,
        "status": "READY",
        "byte_tree_algorithm": prepare.BYTE_TREE_ALGORITHM,
        "source_declaration_sha256": sha256(declaration_bytes),
        "authority_packet_source_path": values["authority_packet_path"],
        "authority_packet_materialized_path": (
            "static/materialized/common/docs/rust-documentation.json"
        ),
        "authority_packet_sha256": sha256(authority.read_bytes()),
        "packages": {
            role: {
                "declared_source_path": declaration["packages"][role]["source_path"],
                "materialized_source_path": packages[role]["source_path"],
                "byte_tree_sha256": packages[role]["byte_tree_sha256"],
                "skill_sha256": packages[role]["skill_sha256"],
            }
            for role in ("v5", "v4")
        },
        "targets": {
            mode: {
                "fixture_id": next(
                    item["fixture_id"]
                    for item in declaration["targets"]
                    if item["mode"] == mode
                ),
                "provenance": next(
                    item["provenance"]
                    for item in declaration["targets"]
                    if item["mode"] == mode
                ),
                "declared_source_path": next(
                    item["source_path"]
                    for item in declaration["targets"]
                    if item["mode"] == mode
                ),
                "materialized_source_path": targets[mode]["source_path"],
                "byte_tree_sha256": targets[mode]["byte_tree_sha256"],
            }
            for mode in prepare.MODES
        },
    }
    if read_json(root / "static" / "integration" / "source-bindings.json") != expected_bindings:
        raise IntegrationError("source bindings do not match exact declarations and identities")
    seeds = prepare.validate_seeds(
        read_json(root / "static" / "generated" / "seeds.json")
    )
    regenerated = prepare.generated_documents(packages, targets, seeds, status="READY")
    documents = {
        name: read_json(root / "static" / "generated" / name) for name in regenerated
    }
    try:
        prepare.verify_generated(documents, seeds, expected_status="READY")
    except (AssertionError, ValueError) as error:
        raise IntegrationError("generated maps/schedule do not regenerate exactly") from error
    generation_binding = {
        "schema_version": 1,
        "status": "READY",
        "source_declaration_sha256": sha256(declaration_bytes),
        "reviewed_values_sha256": sha256(values_bytes),
        "seeds_sha256": sha256(
            (root / "static" / "generated" / "seeds.json").read_bytes()
        ),
        "packages_sha256": sha256(pretty_json_bytes(packages_document)),
        "targets_sha256": sha256(pretty_json_bytes(targets_document)),
        "generated_sha256": {
            name: sha256(pretty_json_bytes(value)) for name, value in documents.items()
        },
    }
    if read_json(root / "static" / "generated" / "generation-binding.json") != generation_binding:
        raise IntegrationError("generation binding does not match exact generated bytes")
    prompts = list((root / "static" / "generated" / "report-prompts").glob("*.md"))
    launches = list((root / "static" / "generated" / "launch-records").glob("*.json"))
    plans = list((root / "static" / "generated" / "report-input-plans").glob("*.json"))
    expected_names = {f"r{index:03d}" for index in range(1, prepare.TOTAL_REPORTS + 1)}
    for paths, suffix, label in (
        (prompts, ".md", "prompts"),
        (launches, ".json", "launch records"),
        (plans, ".json", "input plans"),
    ):
        observed = {path.name.removesuffix(suffix) for path in paths}
        if observed != expected_names:
            raise IntegrationError(f"derived {label} inventory is not exactly r001..r120")
    condition_by_label = {
        row["condition_label"]: row
        for row in documents["condition-map.json"]["conditions"]
    }
    target_by_label = {
        row["target_label"]: row
        for row in documents["target-map.json"]["targets"]
    }
    for slot in documents["launch-schedule.json"]["slots"]:
        run_id = slot["run_id"]
        role = condition_by_label[slot["condition_label"]]["role"]
        scheduled_target = target_by_label[slot["target_label"]]
        plan_path = root / "static" / "generated" / "report-input-plans" / f"{run_id}.json"
        plan = read_json(plan_path)
        validate_schema_file(
            plan,
            RUN / "schemas" / "report-input-plan.schema.json",
            f"report input plan {run_id}",
        )
        if (
            plan["run_id"] != run_id
            or plan["cell_id"] != slot["cell_id"]
            or plan["input_alias"] != prepare.INPUT_ALIAS
            or plan["output_alias"] != prepare.OUTPUT_ALIAS
        ):
            raise IntegrationError(f"report input plan identity drifted: {run_id}")
        validate_agent_visible_mounts(
            root,
            plan,
            condition_role=role,
            packages=packages,
            target=scheduled_target,
            forbidden_tokens=values["forbidden_tokens"],
        )
        launch = read_json(
            root / "static" / "generated" / "launch-records" / f"{run_id}.json"
        )
        if (
            launch.get("assignment_id") != run_id
            or launch.get("run_id") != run_id
            or launch.get("cell_id") != slot["cell_id"]
            or launch.get("condition_role") != role
            or launch.get("schema_paths") != []
            or launch.get("input_packet_sha256") != sha256(plan_path.read_bytes())
            or launch.get("prompt_sha256")
            != sha256(
                (
                    root
                    / "static"
                    / "generated"
                    / "report-prompts"
                    / f"{run_id}.md"
                ).read_bytes()
            )
        ):
            raise IntegrationError(f"report launch record binding drifted: {run_id}")
    execution_root = root / "static" / "execution-manifests"
    if {path.name for path in execution_root.iterdir()} != {
        f"{role}.json" for role in ROLE_NAMES
    }:
        raise IntegrationError("execution-manifest file inventory is not exact")
    execution_digests: dict[str, str] = {}
    for role in ROLE_NAMES:
        expected_manifest = {
            "schema_version": 1,
            "status": "READY",
            "role": role,
            "comparator_parity": "ONE_ROLE_MANIFEST_SHARED_ACROSS_ALL_CONDITIONS",
            **values["execution_environment"][role],
        }
        manifest_path = execution_root / f"{role}.json"
        if read_json(manifest_path) != expected_manifest:
            raise IntegrationError(f"execution manifest does not derive exactly: {role}")
        execution_digests[role] = sha256(manifest_path.read_bytes())

    expected_specs = {
        f"report-{mode}": envelope_spec(
            "report.md", max(4096, values["target_parameters"][mode]["word_cap"] * 16)
        )
        for mode in prepare.MODES
    }
    expected_specs.update(
        {
            "scorer": envelope_spec("score.json", 4 * 1024 * 1024),
            "consistency": envelope_spec("consistency.json", 4 * 1024 * 1024),
            "adjudicator": envelope_spec("adjudication.json", 4 * 1024 * 1024),
            "materiality-reviewer": envelope_spec(
                "materiality-review.json", 4 * 1024 * 1024
            ),
            "materiality-adjudicator": envelope_spec(
                "materiality-adjudication.json", 4 * 1024 * 1024
            ),
        }
    )
    spec_root = root / "static" / "envelope-specs"
    if {path.name for path in spec_root.iterdir()} != {
        *(f"{name}.json" for name in expected_specs),
        "index.json",
    }:
        raise IntegrationError("envelope-spec file inventory is not exact")
    spec_digests: dict[str, str] = {}
    for name, expected_spec in expected_specs.items():
        spec_path = spec_root / f"{name}.json"
        if read_json(spec_path) != expected_spec:
            raise IntegrationError(f"envelope spec does not derive exactly: {name}")
        spec_digests[name] = sha256(spec_path.read_bytes())
    expected_spec_index = {
        "schema_version": 1,
        "status": "READY",
        "spec_sha256": spec_digests,
    }
    if read_json(spec_root / "index.json") != expected_spec_index:
        raise IntegrationError("envelope-spec index does not derive exactly")
    report_material = validate_report_material(
        root,
        documents,
        packages,
        targets,
        values,
        execution_digests,
        spec_digests,
    )
    source_digests = {
        mode: targets[mode]["byte_tree_sha256"] for mode in prepare.MODES
    }
    material_digests = mode_report_material_digests(report_material, documents)
    require_exact_ready_fixture_manifests(
        root,
        reviewed_source_root,
        source_digests=source_digests,
        material_digests=material_digests,
    )
    if reviewed_production_inputs:
        validate_reviewed_semantic_closure(
            root,
            expected_fixture_phase="READY",
            expected_source_digests=source_digests,
            expected_report_material_digests=material_digests,
            evidence_source_root=(
                preserved_inputs / SOURCE_REVIEW_THEOREM_ROOT / "unsafe-rust"
            ),
        )
    expected_evaluator_contract, expected_evaluator_prompts = derive_evaluator_material(
        root, documents, execution_digests, spec_digests
    )
    if read_json(
        root / "static" / "generated" / "evaluator-launch-contracts.json"
    ) != expected_evaluator_contract:
        raise IntegrationError("evaluator launch contract does not derive exactly")
    evaluator_prompt_root = root / "static" / "generated" / "evaluator-prompts"
    observed_evaluator_prompts = {
        path.relative_to(root).as_posix(): path.read_bytes()
        for path in evaluator_prompt_root.iterdir()
        if path.is_file()
    }
    if (
        observed_evaluator_prompts != expected_evaluator_prompts
        or any(path.is_dir() for path in evaluator_prompt_root.rglob("*"))
    ):
        raise IntegrationError("evaluator prompt inventory or bytes do not derive exactly")
    expected_evaluator_receipt = {
        "schema_version": 1,
        "status": "PASS",
        "contract_id": expected_evaluator_contract["contract_id"],
        "assignment_count": len(expected_evaluator_contract["assignments"]),
        "assignment_prompt_sha256": {
            record["assignment_id"]: record["prompt_sha256"]
            for record in expected_evaluator_contract["assignments"]
        },
        "unresolved_marker_count": 0,
    }
    if read_json(
        root / "static" / "generated" / "evaluator-prompt-validation-receipt.json"
    ) != expected_evaluator_receipt:
        raise IntegrationError("evaluator prompt validation receipt does not derive exactly")
    evaluator_schema_paths = {
        path_text
        for record in expected_evaluator_contract["assignments"]
        for path_text in record["schema_paths"]
    }
    for path_text in sorted(evaluator_schema_paths):
        schema = read_json(root / path_text)
        comment = schema.get("$comment") if isinstance(schema, dict) else None
        if (
            not isinstance(comment, str)
            or "DRAFT" in comment
            or "UNSEALED" in comment
        ):
            raise IntegrationError(
                f"agent-visible evaluator schema retains source lifecycle prose: {path_text}"
            )
    validate_snapshot_review_contracts(root)
    word_binding = read_json(
        root / "static" / "integration" / "word-counter-binding.json"
    )
    if word_binding != validate_word_counter(root / "word_count.py"):
        raise IntegrationError("word-counter binding does not match exact staged bytes")
    state = root / RUNTIME_STATE
    if not state.is_dir():
        raise IntegrationError("review snapshot lacks the exact runtime/state carve-out")


def require_empty_runtime_state(root: Path, label: str) -> None:
    state = root / RUNTIME_STATE
    if state.is_symlink() or not state.is_dir():
        raise IntegrationError(f"{label}: runtime/state is not a real directory")
    entries = list(state.iterdir())
    if entries:
        raise IntegrationError(
            f"{label}: runtime/state must be exactly empty before STATIC-LOCK"
        )


def verify_review_snapshot(
    root: Path,
    *,
    expected_candidate_kind: str,
    allow_finalization_artifacts: bool = False,
    require_empty_state: bool = True,
) -> dict[str, Any]:
    if expected_candidate_kind not in BUNDLE_KINDS:
        raise IntegrationError("expected candidate kind is invalid")
    if root.is_symlink() or not root.is_dir():
        raise IntegrationError("review snapshot must be a real directory")
    if require_empty_state:
        require_empty_runtime_state(root, "review snapshot verification")
    if not allow_finalization_artifacts:
        forbidden = [
            path
            for path in (
                root / "INTEGRATION-STATUS.json",
                root / "static" / "integration-receipts",
                root / STATIC_MANIFEST,
                root / STATIC_LOCK,
            )
            if path.exists()
        ]
        if forbidden:
            raise IntegrationError(
                f"review candidate contains finalization artifacts: {forbidden}"
            )
    descriptor_path = root / SNAPSHOT_DESCRIPTOR
    manifest_path = root / SNAPSHOT_MANIFEST
    if descriptor_path.is_symlink() or not descriptor_path.is_file():
        raise IntegrationError(f"missing {SNAPSHOT_DESCRIPTOR}")
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise IntegrationError(f"missing {SNAPSHOT_MANIFEST}")
    descriptor = exact_object(
        read_json(descriptor_path),
        {
            "schema_version",
            "status",
            "candidate_for_bundle_kind",
            "payload_manifest_path",
            "payload_manifest_algorithm",
            "payload_manifest_sha256",
            "payload_entry_count",
            "path_domain",
            "finalization_additions",
        },
        "review snapshot descriptor",
    )
    expected_additions = [
        "INTEGRATION-STATUS.json",
        "static/integration-receipts/**",
        STATIC_MANIFEST,
        STATIC_LOCK,
    ]
    actual_manifest = manifest_path.read_bytes()
    expected_manifest = snapshot_manifest_bytes(root)
    if (
        descriptor["schema_version"] != 1
        or descriptor["status"] != "REVIEW-CANDIDATE"
        or descriptor["candidate_for_bundle_kind"] != expected_candidate_kind
        or descriptor["payload_manifest_path"] != SNAPSHOT_MANIFEST
        or descriptor["payload_manifest_algorithm"] != MANIFEST_ALGORITHM
        or descriptor["payload_manifest_sha256"] != sha256(actual_manifest)
        or descriptor["payload_entry_count"] != count_tree_entries(root, snapshot_excluded)
        or descriptor["path_domain"] != PATH_DOMAIN
        or descriptor["finalization_additions"] != expected_additions
        or actual_manifest != expected_manifest
    ):
        raise IntegrationError("review snapshot does not bind its exact payload")
    validate_schema_file(
        descriptor,
        RUN / "schemas" / "review-snapshot.schema.json",
        SNAPSHOT_DESCRIPTOR,
    )
    validate_hook_inventory(root, expected_status="READY")
    validate_runtime_policy(root, expected_status="READY")
    validate_snapshot_build_products(root, bundle_kind=expected_candidate_kind)
    return descriptor


def create_manifest_and_lock(
    root: Path,
    receipt_sha256: dict[str, str],
    *,
    bundle_kind: str,
) -> dict[str, Any]:
    if (root / STATIC_MANIFEST).exists() or (root / STATIC_LOCK).exists():
        raise IntegrationError("static manifest/lock already exists")
    require_empty_runtime_state(root, "static lock creation")
    normalize_final_permissions(root)
    rendered_manifest = manifest_bytes(root)
    # Temporarily reopen only the root to add the two structural records.
    os.chmod(root, 0o755)
    write_exclusive(root / STATIC_MANIFEST, rendered_manifest)
    os.chmod(root / STATIC_MANIFEST, 0o444)
    snapshot_descriptor_sha = sha256((root / SNAPSHOT_DESCRIPTOR).read_bytes())
    snapshot_manifest_sha = sha256((root / SNAPSHOT_MANIFEST).read_bytes())
    lock = {
        "schema_version": 2,
        "status": "STATIC-LOCKED",
        "bundle_kind": bundle_kind,
        "lock_kind": "IMMUTABLE_PRELAUNCH_STATIC",
        "manifest_path": STATIC_MANIFEST,
        "manifest_algorithm": MANIFEST_ALGORITHM,
        "manifest_sha256": sha256(rendered_manifest),
        "manifest_entry_count": count_tree_entries(root, static_excluded),
        "path_domain": PATH_DOMAIN,
        "metadata_policy": "STATIC_FILES_0444_STATIC_DIRS_0555_RUNTIME_STATE_0700",
        "static_exclusions": [STATIC_MANIFEST, STATIC_LOCK, f"{RUNTIME_STATE}/**"],
        "runtime_carve_out": "EXACT_RUNTIME_STATE_SUBTREE_ONLY",
        "snapshot_descriptor_sha256": snapshot_descriptor_sha,
        "snapshot_manifest_sha256": snapshot_manifest_sha,
        "hook_inventory_sha256": sha256((root / "integration-hooks.json").read_bytes()),
        "receipt_sha256": receipt_sha256,
        "structural_hooks": list(STRUCTURAL_HOOKS),
        "byte_tree_algorithm": prepare.BYTE_TREE_ALGORITHM,
        "last_static_byte_mutation": True,
    }
    validate_schema_file(lock, RUN / "schemas" / "static-lock.schema.json", STATIC_LOCK)
    # This exclusive write is deliberately the final static byte mutation.
    write_exclusive(root / STATIC_LOCK, canonical_json_bytes(lock))
    os.chmod(root / STATIC_LOCK, 0o444)
    os.chmod(root, 0o555)
    fsync_tree(root)
    fsync_directory(root.parent)
    return lock


def _verify_static_contents(
    root: Path,
    *,
    expected_bundle_kind: str,
) -> tuple[dict[str, Any], frozenset[str], dict[str, Any]]:
    if expected_bundle_kind not in BUNDLE_KINDS:
        raise IntegrationError("expected_bundle_kind must be PRODUCTION or SYNTHETIC-TEST-ONLY")
    if root.is_symlink():
        raise IntegrationError("static bundle root must not be a symlink")
    root = root.resolve()
    if not root.is_dir():
        raise IntegrationError("static bundle root must be a real directory")
    manifest_path = root / STATIC_MANIFEST
    lock_path = root / STATIC_LOCK
    if manifest_path.is_symlink() or not manifest_path.is_file():
        raise IntegrationError(f"missing root {STATIC_MANIFEST}")
    if lock_path.is_symlink() or not lock_path.is_file():
        raise IntegrationError(f"missing root {STATIC_LOCK}")
    actual_manifest = manifest_path.read_bytes()
    expected_manifest = manifest_bytes(root)
    if actual_manifest != expected_manifest:
        raise IntegrationError("framed static manifest does not match the exact static tree")
    raw_lock, lock_bytes = read_canonical_read_only_json(
        lock_path, "static lock"
    )
    lock = exact_object(
        raw_lock,
        {
            "schema_version",
            "status",
            "bundle_kind",
            "lock_kind",
            "manifest_path",
            "manifest_algorithm",
            "manifest_sha256",
            "manifest_entry_count",
            "path_domain",
            "metadata_policy",
            "static_exclusions",
            "runtime_carve_out",
            "snapshot_descriptor_sha256",
            "snapshot_manifest_sha256",
            "hook_inventory_sha256",
            "receipt_sha256",
            "structural_hooks",
            "byte_tree_algorithm",
            "last_static_byte_mutation",
        },
        "static lock",
    )
    if (
        lock["schema_version"] != 2
        or lock["status"] != "STATIC-LOCKED"
        or lock["bundle_kind"] != expected_bundle_kind
        or lock["lock_kind"] != "IMMUTABLE_PRELAUNCH_STATIC"
        or lock["manifest_path"] != STATIC_MANIFEST
        or lock["manifest_algorithm"] != MANIFEST_ALGORITHM
        or lock["manifest_sha256"] != sha256(actual_manifest)
        or lock["manifest_entry_count"] != count_tree_entries(root, static_excluded)
        or lock["path_domain"] != PATH_DOMAIN
        or lock["metadata_policy"] != "STATIC_FILES_0444_STATIC_DIRS_0555_RUNTIME_STATE_0700"
        or lock["static_exclusions"] != [STATIC_MANIFEST, STATIC_LOCK, f"{RUNTIME_STATE}/**"]
        or lock["runtime_carve_out"] != "EXACT_RUNTIME_STATE_SUBTREE_ONLY"
        or lock["snapshot_descriptor_sha256"]
        != sha256((root / SNAPSHOT_DESCRIPTOR).read_bytes())
        or lock["snapshot_manifest_sha256"] != sha256((root / SNAPSHOT_MANIFEST).read_bytes())
        or lock["hook_inventory_sha256"] != sha256((root / "integration-hooks.json").read_bytes())
        or lock["structural_hooks"] != list(STRUCTURAL_HOOKS)
        or lock["byte_tree_algorithm"] != prepare.BYTE_TREE_ALGORITHM
        or lock["last_static_byte_mutation"] is not True
    ):
        raise IntegrationError("static lock fields do not bind the verified static bundle")
    validate_schema_file(lock, RUN / "schemas" / "static-lock.schema.json", STATIC_LOCK)
    manifest_records = parse_tree_manifest_records(
        actual_manifest,
        domain=b"ZEROCOPY\0V5\0STATIC-MANIFEST\0V1",
        include_mode=True,
        label="authenticated static manifest",
    )
    descriptor = verify_review_snapshot(
        root,
        expected_candidate_kind=expected_bundle_kind,
        allow_finalization_artifacts=True,
        require_empty_state=False,
    )
    receipt_map = lock["receipt_sha256"]
    if not isinstance(receipt_map, dict) or set(receipt_map) != EXTERNAL_REVIEW_HOOKS:
        raise IntegrationError("static lock snapshot-review receipt set is not exact")
    receipt_index = exact_object(
        read_json(root / "static" / "integration-receipts" / "index.json"),
        {
            "schema_version",
            "status",
            "phase",
            "snapshot_descriptor_sha256",
            "snapshot_manifest_sha256",
            "receipt_sha256",
        },
        "snapshot-review receipt index",
    )
    expected_index = {
        "schema_version": 2,
        "status": "READY",
        "phase": "SNAPSHOT_REVIEW",
        "snapshot_descriptor_sha256": sha256((root / SNAPSHOT_DESCRIPTOR).read_bytes()),
        "snapshot_manifest_sha256": sha256((root / SNAPSHOT_MANIFEST).read_bytes()),
        "receipt_sha256": receipt_map,
    }
    if receipt_index != expected_index:
        raise IntegrationError("receipt index does not equal the static-lock inventory")
    receipt_root = root / "static" / "integration-receipts"
    reject_unsupported_tree(receipt_root, "locked snapshot-review receipt root")
    observed = {
        path.name for path in receipt_root.iterdir() if path.is_file() and path.name != "index.json"
    }
    if observed != {f"{hook_id}.json" for hook_id in EXTERNAL_REVIEW_HOOKS}:
        raise IntegrationError("locked snapshot-review receipt file inventory is not exact")
    if any(path.is_dir() for path in receipt_root.rglob("*")):
        raise IntegrationError("locked snapshot-review receipt root contains a directory")
    captured_snapshot_receipts: dict[str, dict[str, Any]] = {}
    captured_snapshot_bytes: dict[str, bytes] = {}
    synthetic_capability = (
        _SYNTHETIC_CAPABILITY
        if expected_bundle_kind == "SYNTHETIC-TEST-ONLY"
        else None
    )
    for hook_id, expected_sha in receipt_map.items():
        digest(expected_sha, f"lock receipt {hook_id}")
        receipt_path = receipt_root / f"{hook_id}.json"
        receipt, receipt_bytes = _validate_snapshot_review_receipt_captured(
            receipt_path,
            hook_id,
            root,
            descriptor,
            synthetic_capability=synthetic_capability,
        )
        if sha256(receipt_bytes) != expected_sha:
            raise IntegrationError(f"static lock receipt digest mismatch: {hook_id}")
        captured_snapshot_receipts[hook_id] = receipt
        captured_snapshot_bytes[hook_id] = receipt_bytes
    reviewer_ids = frozenset()
    captured_source_receipts: dict[str, dict[str, Any]] = {}
    captured_source_bytes: dict[str, bytes] = {}
    if expected_bundle_kind == "PRODUCTION" or (
        root
        / "static"
        / "integration"
        / "reviewed-inputs"
        / "source-review-receipts"
    ).is_dir():
        reviewed_inputs = root / "static" / "integration" / "reviewed-inputs"
        source_descriptor_bytes = (
            reviewed_inputs / SOURCE_REVIEW_DESCRIPTOR
        ).read_bytes()
        source_manifest_bytes = (
            reviewed_inputs / SOURCE_REVIEW_MANIFEST
        ).read_bytes()
        source_descriptor = parse_json_bytes(
            source_descriptor_bytes, "locked source-review descriptor"
        )
        captured_source_receipts, captured_source_bytes = (
            _validate_source_review_receipts_captured(
                reviewed_inputs / "source-review-receipts",
                snapshot_root=reviewed_inputs,
                descriptor_sha256=sha256(source_descriptor_bytes),
                manifest_sha256=sha256(source_manifest_bytes),
                payload_sha256=source_descriptor["payload_manifest_sha256"],
                synthetic_capability=synthetic_capability,
            )
        )
        for name, receipt_bytes in captured_source_bytes.items():
            relative_path = (
                "static/integration/reviewed-inputs/source-review-receipts/"
                + name
            )
            record = manifest_records.get(relative_path)
            if record != {
                "kind": "F",
                "size": len(receipt_bytes),
                "mode": 0o444,
                "content_sha256": sha256(receipt_bytes),
            }:
                raise IntegrationError(
                    "captured source-review receipt is not the authenticated "
                    f"static-manifest record: {name}"
                )
        reviewer_ids = locked_reviewer_actor_ids(
            captured_source_receipts=captured_source_receipts,
            captured_snapshot_receipts=captured_snapshot_receipts,
        )
    validate_hook_inventory(root, expected_status="READY")
    validate_runtime_policy(root, expected_status="READY")
    validate_integration_status(root, expected_bundle_kind=expected_bundle_kind)
    verify_final_permissions(root)
    if expected_bundle_kind == "PRODUCTION" and len(reviewer_ids) != 11:
        raise IntegrationError(
            "PRODUCTION verifier did not derive eleven reviewer exclusions"
        )
    review_evidence = {
        "schema_version": 1,
        "status": "AUTHENTICATED",
        "algorithm": AUTHENTICATED_REVIEW_EVIDENCE_ALGORITHM,
        "bundle_kind": expected_bundle_kind,
        "static_lock_sha256": sha256(lock_bytes),
        "source_review_receipts": [
            {
                "name": name,
                "receipt_sha256": sha256(captured_source_bytes[name]),
                "receipt": parse_json_bytes(
                    captured_source_bytes[name],
                    f"authenticated source review evidence {name}",
                ),
            }
            for name, _review_kind in SOURCE_REVIEW_KINDS
            if name in captured_source_receipts
        ],
        "snapshot_review_receipts": [
            {
                "hook_id": hook_id,
                "receipt_sha256": sha256(captured_snapshot_bytes[hook_id]),
                "receipt": parse_json_bytes(
                    captured_snapshot_bytes[hook_id],
                    f"authenticated snapshot review evidence {hook_id}",
                ),
            }
            for hook_id in sorted(EXTERNAL_REVIEW_HOOKS)
        ],
    }
    if expected_bundle_kind == "PRODUCTION" and (
        [record["name"] for record in review_evidence["source_review_receipts"]]
        != [name for name, _review_kind in SOURCE_REVIEW_KINDS]
        or [
            record["hook_id"]
            for record in review_evidence["snapshot_review_receipts"]
        ]
        != sorted(EXTERNAL_REVIEW_HOOKS)
    ):
        raise IntegrationError(
            "PRODUCTION verifier did not retain the exact authenticated review evidence"
        )
    return lock, reviewer_ids, review_evidence


def verify_static_with_review_evidence(
    root: Path,
    *,
    expected_bundle_kind: str,
    expected_external_commitment: Any | None = None,
) -> tuple[dict[str, Any], frozenset[str], dict[str, Any]]:
    """Verify static identity and return all same-capture review evidence."""

    if expected_bundle_kind == "PRODUCTION" and expected_external_commitment is None:
        raise IntegrationError(
            "PRODUCTION verification requires a separately custodied external commitment"
        )
    lock, reviewer_ids, review_evidence = _verify_static_contents(
        root, expected_bundle_kind=expected_bundle_kind
    )
    if expected_external_commitment is not None:
        actual_commitment = verify_external_static_commitment(
            root, expected_external_commitment
        )
        if (
            review_evidence["static_lock_sha256"]
            != actual_commitment["static_lock_sha256"]
        ):
            raise IntegrationError(
                "same-capture review evidence does not equal the externally committed lock"
            )
    return lock, reviewer_ids, review_evidence


def verify_static_with_reviewer_ids(
    root: Path,
    *,
    expected_bundle_kind: str,
    expected_external_commitment: Any | None = None,
) -> tuple[dict[str, Any], frozenset[str]]:
    """Verify static identity and return its same-capture reviewer exclusions."""

    lock, reviewer_ids, _review_evidence = verify_static_with_review_evidence(
        root,
        expected_bundle_kind=expected_bundle_kind,
        expected_external_commitment=expected_external_commitment,
    )
    return lock, reviewer_ids


def verify_static(
    root: Path,
    *,
    expected_bundle_kind: str,
    expected_external_commitment: Any | None = None,
) -> dict[str, Any]:
    """Verify a locked bundle, including external identity for PRODUCTION.

    The caller must obtain ``expected_external_commitment`` from separately
    authenticated coordinator custody. Candidate-local bytes cannot satisfy
    this argument. SYNTHETIC-TEST-ONLY bundles have no production identity and
    may be checked without an external commitment.
    """

    lock, _reviewer_ids = verify_static_with_reviewer_ids(
        root,
        expected_bundle_kind=expected_bundle_kind,
        expected_external_commitment=expected_external_commitment,
    )
    return lock


def _verify_static_precommit(
    root: Path, *, expected_bundle_kind: str, capability: object
) -> dict[str, Any]:
    """Private content check before commitment publication or trusted recovery."""

    if (
        capability is not _FINALIZATION_PRECOMMIT_CAPABILITY
        and capability is not _RECOVERY_PRECOMMIT_CAPABILITY
    ):
        raise IntegrationError("uncommitted static verification capability is not authorized")
    lock, _reviewer_ids, _review_evidence = _verify_static_contents(
        root, expected_bundle_kind=expected_bundle_kind
    )
    return lock


def _derive_external_static_commitment(root: Path) -> dict[str, Any]:
    """Derive the coordinator-held commitment for a verified locked bundle."""

    root = root.resolve()
    lock = read_json(root / STATIC_LOCK)
    bundle_kind = lock.get("bundle_kind") if isinstance(lock, dict) else None
    if bundle_kind not in BUNDLE_KINDS:
        raise IntegrationError("cannot commit a bundle with an unknown kind")
    declaration_bytes = (
        trusted_production_declaration_bytes()
        if bundle_kind == "PRODUCTION"
        else (root / "static" / "integration" / "source-declaration.json").read_bytes()
    )
    commitment = {
        "schema_version": 1,
        "status": EXTERNAL_COMMITMENT_STATUS,
        "bundle_kind": bundle_kind,
        "source_declaration_sha256": sha256(declaration_bytes),
        "static_lock_sha256": sha256((root / STATIC_LOCK).read_bytes()),
        "static_manifest_sha256": sha256((root / STATIC_MANIFEST).read_bytes()),
        "snapshot_descriptor_sha256": sha256((root / SNAPSHOT_DESCRIPTOR).read_bytes()),
        "snapshot_manifest_sha256": sha256((root / SNAPSHOT_MANIFEST).read_bytes()),
        "receipt_index_sha256": sha256(
            (root / "static" / "integration-receipts" / "index.json").read_bytes()
        ),
        "integrate_sha256": sha256((root / "integrate.py").read_bytes()),
        "prepare_sha256": sha256((root / "prepare.py").read_bytes()),
        "protocol_sha256": sha256((root / "protocol.py").read_bytes()),
        "word_count_sha256": sha256((root / "word_count.py").read_bytes()),
    }
    validate_schema_file(
        commitment,
        RUN / "schemas" / "external-static-commitment.schema.json",
        "external static commitment",
    )
    return commitment


def verify_external_static_commitment(root: Path, expected: Any) -> dict[str, Any]:
    expected = exact_object(
        expected,
        {
            "schema_version",
            "status",
            "bundle_kind",
            "source_declaration_sha256",
            "static_lock_sha256",
            "static_manifest_sha256",
            "snapshot_descriptor_sha256",
            "snapshot_manifest_sha256",
            "receipt_index_sha256",
            "integrate_sha256",
            "prepare_sha256",
            "protocol_sha256",
            "word_count_sha256",
        },
        "expected external static commitment",
    )
    validate_schema_file(
        expected,
        RUN / "schemas" / "external-static-commitment.schema.json",
        "expected external static commitment",
    )
    actual = _derive_external_static_commitment(root)
    if expected != actual:
        raise IntegrationError(
            "locked bundle does not equal the separately held external commitment"
        )
    return actual


def load_separately_custodied_external_commitment(
    root: Path, commitment_path: Path
) -> dict[str, Any]:
    """Load canonical commitment bytes from a real file outside ``root``."""

    original = Path(os.path.abspath(commitment_path))
    if original.is_symlink() or not original.is_file():
        raise IntegrationError(
            "expected external commitment must be a real regular file"
        )
    commitment = original.resolve(strict=True)
    if root.is_symlink() or not root.is_dir():
        raise IntegrationError("static bundle root must be a real directory")
    bundle = root.resolve(strict=True)
    if paths_overlap(commitment, bundle):
        raise IntegrationError(
            "expected external commitment must be separately custodied outside the bundle"
        )
    data = commitment.read_bytes()
    value = parse_json_bytes(data, "separately custodied external commitment")
    if data != canonical_json_bytes(value):
        raise IntegrationError("external commitment must use canonical JSON bytes")
    return value


def recover_external_commitment(
    *,
    root: Path,
    output: Path,
    custody_acknowledgement: str,
) -> dict[str, Any]:
    """Recover a missing commitment after an interrupted finalization.

    Verification cannot prove that a coherent bundle was not replaced after
    finalization. The acknowledgement is therefore a mandatory, non-mechanical
    assertion that the exact published bundle has remained under uninterrupted
    trusted coordinator custody and that no commitment was previously emitted.
    """

    if custody_acknowledgement != RECOVERY_CUSTODY_ACKNOWLEDGEMENT:
        raise IntegrationError(
            "external-commitment recovery requires acknowledgement of uninterrupted "
            "trusted coordinator custody since successful finalization"
        )
    if root.is_symlink() or not root.is_dir():
        raise IntegrationError("recovery bundle root must be a real directory")
    bundle = root.resolve(strict=True)
    destination = external_commitment_destination(
        bundle, output, "recovery external commitment output"
    )
    _verify_static_precommit(
        bundle,
        expected_bundle_kind="PRODUCTION",
        capability=_RECOVERY_PRECOMMIT_CAPABILITY,
    )
    commitment = _derive_external_static_commitment(bundle)
    # Recheck after deriving the commitment so an ordinary concurrent mutation
    # cannot silently become the recovered identity. Continuity of custody and
    # trusted filesystem behavior remain explicit non-mechanical assumptions.
    _verify_static_precommit(
        bundle,
        expected_bundle_kind="PRODUCTION",
        capability=_RECOVERY_PRECOMMIT_CAPABILITY,
    )
    if _derive_external_static_commitment(bundle) != commitment:
        raise IntegrationError("production bundle changed during commitment recovery")
    _publish_external_commitment_file(destination, commitment)
    verify_static(
        bundle,
        expected_bundle_kind="PRODUCTION",
        expected_external_commitment=commitment,
    )
    return commitment


def validate_source_review_payload(root: Path) -> tuple[dict[str, Any], dict[str, str]]:
    declaration_bytes = trusted_production_declaration_bytes()
    declaration = validate_source_declaration(
        parse_json_bytes(declaration_bytes, "trusted source declaration"),
        production=True,
    )
    values = validate_reviewed_values(
        read_json(root / "reviewed-values.json"),
        declaration_bytes,
        expected_status=SOURCE_REVIEW_CANDIDATE_STATUS,
        require_empty_candidate_static=False,
    )
    prepare.validate_seeds(read_json(root / "seeds.json"))
    support_files = source_review_support_file_map(declaration)
    authority_path_text = relative(values["authority_packet_path"], "authority packet path")
    if authority_path_text != "docs/rust-documentation.json":
        raise IntegrationError("source-review authority packet path is not the fixed agent alias")
    authority_path = root / authority_path_text
    parse_json_bytes(authority_path.read_bytes(), "source-review authority packet")
    expected_payload_files = {
        "reviewed-values.json",
        "seeds.json",
        authority_path_text,
        *(f"reviewed-static/{path}" for path in required_review_paths()),
        *(f"{SOURCE_REVIEW_CONTRACT_ROOT}/{name}" for name, _kind in SOURCE_REVIEW_KINDS),
        *support_files,
    }
    observed_payload_files = {
        path.relative_to(root).as_posix()
        for path in root.rglob("*")
        if path.is_file() and not source_review_excluded(path.relative_to(root))
    }
    if observed_payload_files != expected_payload_files:
        raise IntegrationError(
            "source-review payload inventory is not exact; "
            f"missing={sorted(expected_payload_files - observed_payload_files)}, "
            f"extra={sorted(observed_payload_files - expected_payload_files)}"
        )
    observed_payload_directories = {
        path.relative_to(root).as_posix()
        for path in root.rglob("*")
        if path.is_dir() and not source_review_excluded(path.relative_to(root))
    }
    expected_payload_directories: set[str] = set()
    for path_text in expected_payload_files:
        parent = Path(path_text).parent
        while parent != Path("."):
            expected_payload_directories.add(parent.as_posix())
            parent = parent.parent
    if observed_payload_directories != expected_payload_directories:
        raise IntegrationError(
            "source-review payload directory inventory is not exact; "
            f"missing={sorted(expected_payload_directories - observed_payload_directories)}, "
            f"extra={sorted(observed_payload_directories - expected_payload_directories)}"
        )
    for path_text, data in support_files.items():
        path = root / path_text
        if path.is_symlink() or not path.is_file() or path.read_bytes() != data:
            raise IntegrationError(
                f"source-review support/theorem input drifted: {path_text}"
            )
    for record in declaration["targets"]:
        source_path = relative(record["source_path"], "source-review target path")
        copied_target = (
            root / SOURCE_REVIEW_THEOREM_ROOT / "unsafe-rust" / source_path
        )
        _trusted_path, expected_tree_sha256 = trusted_declared_tree(
            source_path, f"source-review target {record['mode']}"
        )
        if prepare.byte_tree_v1(copied_target) != expected_tree_sha256:
            raise IntegrationError(
                f"source-review target tree does not match trusted identity: {record['mode']}"
            )
    source_digests = trusted_target_source_digests(declaration)
    expected_static = derive_reviewed_static_files(
        target_source_digests=source_digests
    )
    overlay = root / "reviewed-static"
    observed_static = {
        path.relative_to(overlay).as_posix(): path.read_bytes()
        for path in overlay.rglob("*")
        if path.is_file()
    }
    if observed_static != expected_static:
        raise IntegrationError("source-review static bytes are not the exact trusted transition")
    if values["reviewed_static"] != reviewed_static_records(
        expected_static, decision="PENDING"
    ):
        raise IntegrationError("reviewed-values does not bind the exact reviewed-static bytes")
    expected_authority = expected_static[
        "freeze/authority/agent-visible/common.json"
    ]
    if authority_path.read_bytes() != expected_authority:
        raise IntegrationError(
            "source-review authority packet differs from the canonical reviewed projection"
        )
    validate_reviewed_static(
        overlay, values["reviewed_static"], expected_decision="PENDING"
    )
    validate_reviewed_semantic_closure(
        overlay,
        expected_fixture_phase="SOURCE_REVIEW_CANDIDATE",
        expected_source_digests=source_digests,
        evidence_source_root=(
            root / SOURCE_REVIEW_THEOREM_ROOT / "unsafe-rust"
        ),
    )
    validate_source_review_contracts(root)
    return values, source_digests


def create_source_review_snapshot(root: Path) -> dict[str, Any]:
    if any((root / name).exists() for name in (SOURCE_REVIEW_MANIFEST, SOURCE_REVIEW_DESCRIPTOR)):
        raise IntegrationError("source-review snapshot records already exist")
    if (root / "source-review-receipts").exists():
        raise IntegrationError("source-review candidate already contains receipts")
    validate_source_review_payload(root)
    contracts = validate_source_review_contracts(root)
    payload = source_review_manifest_bytes(root)
    write_exclusive(root / SOURCE_REVIEW_MANIFEST, payload)
    descriptor = {
        "schema_version": 1,
        "status": "REVIEW-CANDIDATE",
        "review_kind": "V5-REVIEWED-SOURCE-INPUTS",
        "payload_manifest_path": SOURCE_REVIEW_MANIFEST,
        "payload_manifest_algorithm": MANIFEST_ALGORITHM,
        "payload_manifest_sha256": sha256(payload),
        "payload_entry_count": count_tree_entries(root, source_review_excluded),
        "path_domain": PATH_DOMAIN,
        "required_reviews": [
            {
                "file": name,
                "review_kind": kind,
                "contract_path": f"{SOURCE_REVIEW_CONTRACT_ROOT}/{name}",
                "contract_sha256": sha256(
                    pretty_json_bytes(contracts[name])
                ),
            }
            for name, kind in SOURCE_REVIEW_KINDS
        ],
        "finalization_additions": ["source-review-receipts/**"],
    }
    validate_schema_file(
        descriptor,
        RUN / "schemas" / "source-review-snapshot.schema.json",
        SOURCE_REVIEW_DESCRIPTOR,
    )
    write_json(root / SOURCE_REVIEW_DESCRIPTOR, descriptor)
    normalize_read_only_review_tree(root)
    fsync_tree(root)
    return descriptor


def verify_source_review_snapshot(
    root: Path,
    *,
    require_receipts: bool,
    require_read_only: bool = True,
    synthetic_capability: object | None = None,
) -> dict[str, Any]:
    if root.is_symlink() or not root.is_dir():
        raise IntegrationError("source-review snapshot must be a real directory")
    descriptor = read_json(root / SOURCE_REVIEW_DESCRIPTOR)
    validate_schema_file(
        descriptor,
        RUN / "schemas" / "source-review-snapshot.schema.json",
        SOURCE_REVIEW_DESCRIPTOR,
    )
    expected_descriptor = {
        "schema_version": 1,
        "status": "REVIEW-CANDIDATE",
        "review_kind": "V5-REVIEWED-SOURCE-INPUTS",
        "payload_manifest_path": SOURCE_REVIEW_MANIFEST,
        "payload_manifest_algorithm": MANIFEST_ALGORITHM,
        "payload_manifest_sha256": sha256(
            (root / SOURCE_REVIEW_MANIFEST).read_bytes()
        ),
        "payload_entry_count": count_tree_entries(root, source_review_excluded),
        "path_domain": PATH_DOMAIN,
        "required_reviews": [
            {
                "file": name,
                "review_kind": kind,
                "contract_path": f"{SOURCE_REVIEW_CONTRACT_ROOT}/{name}",
                "contract_sha256": sha256(
                    (root / SOURCE_REVIEW_CONTRACT_ROOT / name).read_bytes()
                ),
            }
            for name, kind in SOURCE_REVIEW_KINDS
        ],
        "finalization_additions": ["source-review-receipts/**"],
    }
    if descriptor != expected_descriptor:
        raise IntegrationError("source-review descriptor is not exact")
    if (root / SOURCE_REVIEW_MANIFEST).read_bytes() != source_review_manifest_bytes(root):
        raise IntegrationError("source-review manifest does not bind the exact payload")
    validate_source_review_payload(root)
    receipt_root = root / "source-review-receipts"
    if require_receipts:
        validate_source_review_receipts(
            receipt_root,
            snapshot_root=root,
            descriptor_sha256=sha256((root / SOURCE_REVIEW_DESCRIPTOR).read_bytes()),
            manifest_sha256=sha256((root / SOURCE_REVIEW_MANIFEST).read_bytes()),
            payload_sha256=descriptor["payload_manifest_sha256"],
            synthetic_capability=synthetic_capability,
        )
    elif receipt_root.exists():
        raise IntegrationError("unfinalized source-review candidate contains receipts")
    if require_read_only:
        verify_read_only_review_tree(root)
    return descriptor


def prepare_source_review(
    *, source_root: Path, inputs: Path, output: Path
) -> None:
    source_root = source_root.resolve()
    inputs = inputs.resolve()
    output = output.resolve()
    if source_root != trusted_unsafe_rust_root():
        raise IntegrationError("production source review requires the exact trusted source root")
    if any(paths_overlap(first, second) for first, second in ((inputs, source_root), (output, source_root), (output, inputs))):
        raise IntegrationError("source-review paths must be mutually disjoint")
    if output.exists():
        raise IntegrationError("source-review output already exists")
    reject_unsupported_tree(inputs, "source-review input root")
    declaration_bytes = trusted_production_declaration_bytes()
    candidate_values = validate_reviewed_values(
        read_json(inputs / "reviewed-values.json"),
        declaration_bytes,
        expected_status="SOURCE-REVIEW-CANDIDATE",
    )
    seeds_bytes = (inputs / "seeds.json").read_bytes()
    prepare.validate_seeds(parse_json_bytes(seeds_bytes, "source-review seeds"))
    authority_path_text = relative(
        candidate_values["authority_packet_path"], "authority packet path"
    )
    if authority_path_text != "docs/rust-documentation.json":
        raise IntegrationError("source-review authority packet path must use the fixed alias")
    expected_inputs = {"reviewed-values.json", "seeds.json"}
    observed_inputs = {
        path.relative_to(inputs).as_posix()
        for path in inputs.rglob("*")
        if path.is_file()
    }
    if observed_inputs != expected_inputs:
        raise IntegrationError("source-review input file inventory is not exact")
    declaration = validate_source_declaration(
        parse_json_bytes(declaration_bytes, "trusted source declaration"),
        production=True,
    )
    static_files = derive_reviewed_static_files(
        target_source_digests=trusted_target_source_digests(declaration)
    )
    authority_bytes = static_files["freeze/authority/agent-visible/common.json"]
    candidate_snapshot_values = {
        **candidate_values,
        "status": SOURCE_REVIEW_CANDIDATE_STATUS,
        "reviewed_static_base": REVIEWED_STATIC_CANDIDATE_BASE,
        "reviewed_static": reviewed_static_records(
            static_files, decision="PENDING"
        ),
    }
    output.parent.mkdir(parents=True, exist_ok=True)
    fsync_directory(output.parent)
    stage = Path(tempfile.mkdtemp(prefix=".v5-source-review-stage-", dir=output.parent))
    try:
        write_exclusive(
            stage / "reviewed-values.json",
            pretty_json_bytes(candidate_snapshot_values),
        )
        write_exclusive(stage / "seeds.json", seeds_bytes)
        write_exclusive(stage / authority_path_text, authority_bytes)
        for path_text, data in static_files.items():
            write_exclusive(stage / "reviewed-static" / path_text, data)
        materialize_source_review_support(stage, declaration)
        build_source_review_contracts(stage)
        create_source_review_snapshot(stage)
        verify_source_review_snapshot(stage, require_receipts=False)
        publish_no_replace(stage, output)
    except Exception:
        if stage.exists():
            make_tree_writable(stage)
            shutil.rmtree(stage, ignore_errors=True)
        raise


def prepare_source_review_copy(snapshot: Path, private_copy: Path) -> dict[str, Any]:
    snapshot = snapshot.resolve()
    private_copy = private_copy.resolve()
    if paths_overlap(snapshot, private_copy) or private_copy.exists():
        raise IntegrationError("source-review private copy must be fresh and disjoint")
    before = verify_source_review_snapshot(snapshot, require_receipts=False)
    private_copy.parent.mkdir(parents=True, exist_ok=True)
    fsync_directory(private_copy.parent)
    stage = Path(tempfile.mkdtemp(prefix=".v5-source-review-copy-", dir=private_copy.parent))
    try:
        stage.rmdir()
        copy_tree(snapshot, stage)
        if verify_source_review_snapshot(stage, require_receipts=False) != before:
            raise IntegrationError("source-review private copy changed during copy")
        if verify_source_review_snapshot(snapshot, require_receipts=False) != before:
            raise IntegrationError("source-review snapshot changed while copied")
        publish_no_replace(stage, private_copy)
    except Exception:
        if stage.exists():
            make_tree_writable(stage)
            shutil.rmtree(stage, ignore_errors=True)
        raise
    return before


def verify_source_review_custody(snapshot: Path, private_copy: Path) -> dict[str, Any]:
    snapshot, private_copy = require_disjoint_review_subjects(
        snapshot, private_copy, "source review"
    )
    source = verify_source_review_snapshot(snapshot, require_receipts=False)
    private = verify_source_review_snapshot(private_copy, require_receipts=False)
    if source != private or (snapshot / SOURCE_REVIEW_MANIFEST).read_bytes() != (private_copy / SOURCE_REVIEW_MANIFEST).read_bytes():
        raise IntegrationError("source-review source and private copy no longer agree")
    return private


def verify_source_review_quotations(
    private_copy: Path,
    *,
    online_validator: Callable[..., str] | None = None,
) -> str:
    """Run the network quotation check over an authenticated candidate copy.

    ``online_validator`` is an internal self-test seam; the public CLI never
    accepts or imports reviewer-supplied executable code.
    """

    private_copy = private_copy.resolve()
    verify_source_review_snapshot(private_copy, require_receipts=False)
    if online_validator is None:
        validator = runpy.run_path(
            str(RUN / "freeze" / "validate_oracle_materials.py"),
            run_name="v5_online_exact_quotation_review",
        )
        online_validator = validator["verify_exact_quotations_online"]
    result = online_validator(
        private_copy / "reviewed-static" / "freeze",
        expected_status=SOURCE_REVIEW_CANDIDATE_STATUS,
        supplied_source_root=(
            private_copy / SOURCE_REVIEW_THEOREM_ROOT / "unsafe-rust"
        ),
    )
    if result != EXACT_QUOTATION_EVIDENCE_SHA256:
        raise IntegrationError("online exact-quotation evidence digest drifted")
    return result


def build_source_review_receipt(
    *,
    snapshot: Path,
    private_copy: Path,
    review_name: str,
    actor_id: str,
    work_product_path: Path,
    result_path: Path,
    output: Path,
) -> dict[str, Any]:
    """Bind reviewer-authored findings into one exact production receipt."""

    review_kind_by_name = dict(SOURCE_REVIEW_KINDS)
    if review_name not in review_kind_by_name:
        raise IntegrationError("source-review receipt name is not recognized")
    if output.name != review_name:
        raise IntegrationError("source-review receipt filename must equal its review name")
    identity = require_actor_id(actor_id, "source reviewer actor")
    snapshot = snapshot.resolve()
    private_copy = private_copy.resolve()
    destination = Path(os.path.abspath(output)).parent.resolve() / output.name
    if paths_overlap(destination, snapshot) or paths_overlap(destination, private_copy):
        raise IntegrationError("source-review receipt must be outside both review copies")
    before = verify_source_review_custody(snapshot, private_copy)
    contracts = validate_source_review_contracts(private_copy)
    contract = contracts[review_name]
    review_kind = review_kind_by_name[review_name]
    reviewer_runtime = current_reviewer_runtime_attestation()
    work_product, work_product_sha256 = validate_review_work_product(
        read_json(work_product_path),
        expected_coverage_items=contract["coverage_items"],
    )
    descriptor_sha256 = sha256(
        (private_copy / SOURCE_REVIEW_DESCRIPTOR).read_bytes()
    )
    manifest_sha256 = sha256(
        (private_copy / SOURCE_REVIEW_MANIFEST).read_bytes()
    )
    payload_sha256 = before["payload_manifest_sha256"]
    contract_path = f"{SOURCE_REVIEW_CONTRACT_ROOT}/{review_name}"
    expected_inputs = {
        SOURCE_REVIEW_DESCRIPTOR: descriptor_sha256,
        SOURCE_REVIEW_MANIFEST: manifest_sha256,
        contract_path: sha256((private_copy / contract_path).read_bytes()),
        contract["procedure_path"]: contract["procedure_sha256"],
        contract["receipt_schema_path"]: contract["receipt_schema_sha256"],
        "trusted-reviewer-tool-set": contract["reviewer_tool_set_sha256"],
        "reviewer-runtime-attestation": sha256(
            canonical_json_bytes(reviewer_runtime)
        ),
    }
    result = validate_source_review_result(
        read_json(result_path),
        label=review_name,
        review_kind=review_kind,
        contract=contract,
        descriptor_sha256=descriptor_sha256,
        manifest_sha256=manifest_sha256,
        payload_sha256=payload_sha256,
        expected_inputs=expected_inputs,
    )
    receipt = {
        "schema_version": 1,
        "status": "PASS",
        "review_kind": review_kind,
        "actor": {
            "identity": identity,
            "role": "INDEPENDENT_REVIEWER",
            "implementation": contract["procedure_id"],
            "version": contract["procedure_version"],
        },
        "reviewer_runtime": reviewer_runtime,
        "input_digests": expected_inputs,
        "output_digests": {
            "reviewed-payload-manifest": payload_sha256,
            "reviewed-artifact-set": contract["artifact_set_sha256"],
            "review-work-product": work_product_sha256,
        },
        "work_product": work_product,
        "result": result,
    }
    validate_schema_file(
        receipt,
        RUN / "schemas" / "source-review-receipt.schema.json",
        f"source review receipt {review_name}",
    )
    if verify_source_review_custody(snapshot, private_copy) != before:
        raise IntegrationError("source-review subject changed while receipt was built")
    publish_read_only_canonical_json(
        destination, receipt, label="source-review receipt output"
    )
    return receipt


def validate_production_source_review_receipts(
    *, snapshot: Path, receipts: Path
) -> dict[str, dict[str, Any]]:
    snapshot = snapshot.resolve()
    descriptor = verify_source_review_snapshot(
        snapshot, require_receipts=False
    )
    return validate_source_review_receipts(
        receipts.resolve(),
        snapshot_root=snapshot,
        descriptor_sha256=sha256((snapshot / SOURCE_REVIEW_DESCRIPTOR).read_bytes()),
        manifest_sha256=sha256((snapshot / SOURCE_REVIEW_MANIFEST).read_bytes()),
        payload_sha256=descriptor["payload_manifest_sha256"],
    )


def _finalize_reviewed_inputs(
    *,
    snapshot: Path,
    receipts: Path,
    output: Path,
    synthetic_capability: object | None,
) -> None:
    if synthetic_capability not in {None, _SYNTHETIC_CAPABILITY}:
        raise IntegrationError("unrecognized synthetic source-review capability")
    snapshot = snapshot.resolve()
    receipts = receipts.resolve()
    output = output.resolve()
    if any(paths_overlap(first, second) for first, second in ((snapshot, receipts), (snapshot, output), (receipts, output))):
        raise IntegrationError("source-review snapshot, receipts, and output must be disjoint")
    if output.exists():
        raise IntegrationError("reviewed-input output already exists")
    descriptor = verify_source_review_snapshot(snapshot, require_receipts=False)
    validated, captured_receipts = _validate_source_review_receipts_captured(
        receipts,
        snapshot_root=snapshot,
        descriptor_sha256=sha256((snapshot / SOURCE_REVIEW_DESCRIPTOR).read_bytes()),
        manifest_sha256=sha256((snapshot / SOURCE_REVIEW_MANIFEST).read_bytes()),
        payload_sha256=descriptor["payload_manifest_sha256"],
        synthetic_capability=synthetic_capability,
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    fsync_directory(output.parent)
    stage = Path(tempfile.mkdtemp(prefix=".v5-reviewed-inputs-stage-", dir=output.parent))
    try:
        stage.rmdir()
        copy_tree(snapshot, stage)
        make_tree_writable(stage)
        for name, review in validated.items():
            receipt_bytes = captured_receipts[name]
            if parse_json_bytes(receipt_bytes, f"captured source review receipt {name}") != review:
                raise IntegrationError("captured source-review receipt bytes drifted")
            write_exclusive(
                stage / "source-review-receipts" / name,
                receipt_bytes,
            )
        normalize_read_only_review_tree(stage)
        fsync_tree(stage)
        verify_source_review_snapshot(
            stage,
            require_receipts=True,
            synthetic_capability=synthetic_capability,
        )
        publish_no_replace(stage, output)
    except Exception:
        if stage.exists():
            make_tree_writable(stage)
            shutil.rmtree(stage, ignore_errors=True)
        raise


def finalize_reviewed_inputs(
    *, snapshot: Path, receipts: Path, output: Path
) -> None:
    _finalize_reviewed_inputs(
        snapshot=snapshot,
        receipts=receipts,
        output=output,
        synthetic_capability=None,
    )


def prepare_private_review_copy(snapshot: Path, private_copy: Path) -> dict[str, Any]:
    """Make and verify the reviewer's private custody copy of a PRODUCTION snapshot."""

    snapshot = snapshot.resolve()
    private_copy = private_copy.resolve()
    if paths_overlap(snapshot, private_copy):
        raise IntegrationError("review snapshot and private review copy must be disjoint")
    if private_copy.exists():
        raise IntegrationError(f"private review copy already exists: {private_copy}")
    before = verify_review_snapshot(snapshot, expected_candidate_kind="PRODUCTION")
    private_copy.parent.mkdir(parents=True, exist_ok=True)
    fsync_directory(private_copy.parent)
    stage = Path(
        tempfile.mkdtemp(prefix=".v5-private-review-stage-", dir=private_copy.parent)
    )
    try:
        stage.rmdir()
        copy_tree(snapshot, stage)
        copied = verify_review_snapshot(stage, expected_candidate_kind="PRODUCTION")
        if copied != before:
            raise IntegrationError("private review copy descriptor changed during copy")
        normalize_final_permissions(stage)
        fsync_tree(stage)
        # Reverify the source immediately before no-replace publication.  The
        # independent actor must retain custody of the private copy and perform
        # the paired end-of-review re-verification required by its contract.
        if verify_review_snapshot(
            snapshot, expected_candidate_kind="PRODUCTION"
        ) != before:
            raise IntegrationError("source snapshot changed while private copy was made")
        publish_no_replace(stage, private_copy)
        if verify_review_snapshot(
            private_copy, expected_candidate_kind="PRODUCTION"
        ) != before:
            raise IntegrationError("published private review copy failed verification")
    except Exception:
        if stage.exists():
            make_tree_writable(stage)
            shutil.rmtree(stage, ignore_errors=True)
        raise
    return before


def verify_private_review_custody(snapshot: Path, private_copy: Path) -> dict[str, Any]:
    """Perform the required paired end-of-review snapshot verification."""

    snapshot, private_copy = require_disjoint_review_subjects(
        snapshot, private_copy, "snapshot review"
    )
    source_descriptor = verify_review_snapshot(
        snapshot, expected_candidate_kind="PRODUCTION"
    )
    private_descriptor = verify_review_snapshot(
        private_copy, expected_candidate_kind="PRODUCTION"
    )
    if source_descriptor != private_descriptor:
        raise IntegrationError("source snapshot and private review copy no longer agree")
    if snapshot_manifest_bytes(snapshot) != snapshot_manifest_bytes(
        private_copy
    ):
        raise IntegrationError("source snapshot and private review copy payloads differ")
    return private_descriptor


def build_snapshot_review_receipt(
    *,
    snapshot: Path,
    private_copy: Path,
    hook_id: str,
    actor_id: str,
    work_product_path: Path,
    result_path: Path,
    output: Path,
) -> dict[str, Any]:
    """Bind reviewer-authored findings into one exact snapshot receipt."""

    if hook_id not in EXTERNAL_REVIEW_HOOKS:
        raise IntegrationError("snapshot-review hook is not recognized")
    if output.name != f"{hook_id}.json":
        raise IntegrationError("snapshot-review receipt filename must equal its hook ID")
    identity = require_actor_id(actor_id, "snapshot reviewer actor")
    snapshot = snapshot.resolve()
    private_copy = private_copy.resolve()
    destination = Path(os.path.abspath(output)).parent.resolve() / output.name
    if paths_overlap(destination, snapshot) or paths_overlap(destination, private_copy):
        raise IntegrationError("snapshot-review receipt must be outside both review copies")
    before = verify_private_review_custody(snapshot, private_copy)
    contract = validate_snapshot_review_contracts(private_copy)[hook_id]
    reviewer_runtime = current_reviewer_runtime_attestation()
    work_product, work_product_sha256 = validate_review_work_product(
        read_json(work_product_path),
        expected_coverage_items=contract["coverage_items"],
    )
    receipt = {
        "schema_version": 2,
        "status": "PASS",
        "phase": "SNAPSHOT_REVIEW",
        "hook_id": hook_id,
        "receipt_kind": "INDEPENDENT_SNAPSHOT_REVIEW",
        "actor": {
            "identity": identity,
            "role": "INDEPENDENT_REVIEWER",
            "implementation": contract["procedure_id"],
            "version": contract["procedure_version"],
        },
        "reviewer_runtime": reviewer_runtime,
        "input_digests": snapshot_receipt_inputs(
            private_copy, hook_id, reviewer_runtime=reviewer_runtime
        ),
        "output_digests": {
            "reviewed-payload-manifest": before["payload_manifest_sha256"],
            "reviewed-artifact-set": contract["artifact_set_sha256"],
            "review-work-product": work_product_sha256,
        },
        "work_product": work_product,
        "result": read_json(result_path),
    }
    destination.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(
        prefix=".v5-snapshot-receipt-validation-", dir=destination.parent
    ) as directory:
        validation_path = Path(directory) / output.name
        validation_path.write_bytes(canonical_json_bytes(receipt))
        os.chmod(validation_path, 0o444)
        validated = validate_snapshot_review_receipt(
            validation_path,
            hook_id,
            private_copy,
            before,
        )
    if verify_private_review_custody(snapshot, private_copy) != before:
        raise IntegrationError("snapshot-review subject changed while receipt was built")
    publish_read_only_canonical_json(
        destination, validated, label="snapshot-review receipt output"
    )
    return validated


def validate_production_snapshot_review_receipts(
    *, snapshot: Path, receipts: Path
) -> dict[str, dict[str, Any]]:
    snapshot = snapshot.resolve()
    receipts = receipts.resolve()
    descriptor = verify_review_snapshot(
        snapshot, expected_candidate_kind="PRODUCTION"
    )
    if receipts.is_symlink() or not receipts.is_dir():
        raise IntegrationError("snapshot-review receipt root must be a real directory")
    reject_unsupported_tree(receipts, "snapshot-review receipt root")
    expected_names = {f"{hook_id}.json" for hook_id in EXTERNAL_REVIEW_HOOKS}
    entries = list(receipts.iterdir())
    observed_names = {
        path.name for path in entries if stat.S_ISREG(path.lstat().st_mode)
    }
    if observed_names != expected_names or len(entries) != len(expected_names):
        raise IntegrationError("snapshot-review receipt inventory is not exact")
    validated = {
        hook_id: validate_snapshot_review_receipt(
            receipts / f"{hook_id}.json",
            hook_id,
            snapshot,
            descriptor,
        )
        for hook_id in sorted(EXTERNAL_REVIEW_HOOKS)
    }
    snapshot_actor_ids = {
        receipt["actor"]["identity"] for receipt in validated.values()
    }
    if len(snapshot_actor_ids) != len(EXTERNAL_REVIEW_HOOKS):
        raise IntegrationError("snapshot reviewer identities must be pairwise distinct")
    source_receipt_root = (
        snapshot
        / "static/integration/reviewed-inputs/source-review-receipts"
    )
    source_actor_ids = {
        read_json(source_receipt_root / name)["actor"]["identity"]
        for name, _review_kind in SOURCE_REVIEW_KINDS
    }
    if len(source_actor_ids) != len(SOURCE_REVIEW_KINDS):
        raise IntegrationError("source reviewer identities are not pairwise distinct")
    if source_actor_ids.intersection(snapshot_actor_ids):
        raise IntegrationError("source and snapshot reviewer identities must be disjoint")
    return validated


def _prepare_snapshot(
    *,
    source_root: Path,
    inputs: Path,
    output: Path,
    workspace_base: Path,
    declaration_path: Path,
    bundle_kind: str,
    synthetic_capability: object | None,
) -> None:
    if bundle_kind == "PRODUCTION":
        if synthetic_capability is not None or declaration_path.resolve() != SOURCE_DECLARATION.resolve():
            raise IntegrationError("only the real source declaration may prepare PRODUCTION")
    elif bundle_kind == "SYNTHETIC-TEST-ONLY":
        if synthetic_capability is not _SYNTHETIC_CAPABILITY:
            raise IntegrationError("synthetic bundle preparation is private to self-test")
    else:
        raise IntegrationError("unknown bundle kind")
    if source_root.is_symlink() or inputs.is_symlink() or output.is_symlink():
        raise IntegrationError("source, input, and output roots must not be symlinks")
    source_root = source_root.resolve()
    inputs = inputs.resolve()
    output = output.resolve()
    runtime_policy = validate_runtime_policy(RUN, expected_status="DRAFT")
    forbidden_path_terms = runtime_policy["agent_visible_path_forbidden_terms"]
    workspace_base = require_neutral_workspace_base(workspace_base, forbidden_path_terms)
    if RUN == output or RUN in output.parents or output in RUN.parents:
        raise IntegrationError("integrated output must be outside the DRAFT source run")
    for first, second, label in (
        (inputs, source_root, "reviewed inputs and source root"),
        (output, source_root, "integrated output and source root"),
        (output, inputs, "integrated output and reviewed inputs"),
        (workspace_base, source_root, "agent workspace and source root"),
        (workspace_base, inputs, "agent workspace and reviewed inputs"),
        (workspace_base, output, "agent workspace and integrated output"),
    ):
        if paths_overlap(first, second):
            raise IntegrationError(f"path isolation requires disjoint {label}")
    if output.exists():
        raise IntegrationError(f"integrated output already exists: {output}")
    if workspace_base.exists():
        raise IntegrationError(
            f"agent workspace base must be fresh and absent at integration: {workspace_base}"
        )
    reject_unsupported_tree(source_root, "unsafe-rust source root")
    reject_unsupported_tree(inputs, "reviewed integration input root")
    declaration_bytes = declaration_path.read_bytes()
    trusted_production_inputs = (
        declaration_bytes == trusted_production_declaration_bytes()
        and source_root == trusted_unsafe_rust_root()
    )
    production_declaration = bundle_kind == "PRODUCTION"
    reviewed_production_inputs = production_declaration or (
        bundle_kind == "SYNTHETIC-TEST-ONLY"
        and synthetic_capability is _SYNTHETIC_CAPABILITY
        and trusted_production_inputs
    )
    if production_declaration and not trusted_production_inputs:
        raise IntegrationError(
            "PRODUCTION preparation inputs changed from trusted source/declaration"
        )
    declaration = validate_source_declaration(
        parse_json_bytes(declaration_bytes, str(declaration_path)),
        production=reviewed_production_inputs,
    )
    if reviewed_production_inputs:
        verify_source_review_snapshot(
            inputs,
            require_receipts=True,
            synthetic_capability=(
                _SYNTHETIC_CAPABILITY
                if bundle_kind == "SYNTHETIC-TEST-ONLY"
                else None
            ),
        )
    reviewed_path = inputs / "reviewed-values.json"
    source_reviewed_bytes = reviewed_path.read_bytes()
    source_reviewed_value = parse_json_bytes(source_reviewed_bytes, str(reviewed_path))
    if reviewed_production_inputs:
        source_reviewed = validate_reviewed_values(
            source_reviewed_value,
            declaration_bytes,
            expected_status=SOURCE_REVIEW_CANDIDATE_STATUS,
            require_empty_candidate_static=False,
        )
        reviewed_source_files = {
            record["path"]: (
                inputs / "reviewed-static" / record["path"]
            ).read_bytes()
            for record in source_reviewed["reviewed_static"]
        }
        reviewed = {
            **source_reviewed,
            "status": "READY",
            "reviewed_static_base": REVIEWED_STATIC_BUNDLE_BASE,
            "reviewed_static": reviewed_static_records(
                reviewed_source_files, decision="PASS"
            ),
        }
        reviewed_bytes = pretty_json_bytes(reviewed)
    else:
        reviewed = validate_reviewed_values(source_reviewed_value, declaration_bytes)
        reviewed = {
            **reviewed,
            "reviewed_static_base": REVIEWED_STATIC_BUNDLE_BASE,
        }
        reviewed_bytes = pretty_json_bytes(reviewed)
    seeds_path = inputs / "seeds.json"
    seeds_bytes = seeds_path.read_bytes()
    seeds = prepare.validate_seeds(parse_json_bytes(seeds_bytes, str(seeds_path)))
    output.parent.mkdir(parents=True, exist_ok=True)
    fsync_directory(output.parent)
    stage = Path(tempfile.mkdtemp(prefix=".v5-review-snapshot-stage-", dir=output.parent))
    try:
        reject_unsupported_tree(RUN, "DRAFT harness source")
        source_copy_digest = sha256(source_copy_manifest_bytes(RUN))
        stage.rmdir()
        shutil.copytree(RUN, stage, ignore=source_copy_ignore, symlinks=False)
        if sha256(source_copy_manifest_bytes(stage)) != source_copy_digest:
            raise IntegrationError("DRAFT harness source changed while it was copied")
        promote_operational_metadata(stage)
        preserved_reviewed_inputs = (
            stage / "static" / "integration" / "reviewed-inputs"
        )
        if reviewed_production_inputs:
            copy_tree(inputs, preserved_reviewed_inputs)
            verify_source_review_snapshot(
                preserved_reviewed_inputs,
                require_receipts=True,
                synthetic_capability=(
                    _SYNTHETIC_CAPABILITY
                    if bundle_kind == "SYNTHETIC-TEST-ONLY"
                    else None
                ),
            )
        overlay = inputs / "reviewed-static"
        reject_unsupported_tree(overlay, "reviewed static overlay")
        overlay_files = {
            path.relative_to(overlay).as_posix()
            for path in overlay.rglob("*")
            if path.is_file()
        }
        overlay_directories = {
            path.relative_to(overlay).as_posix()
            for path in overlay.rglob("*")
            if path.is_dir()
        }
        expected_overlay_directories: set[str] = set()
        for path_text in required_review_paths():
            parent = Path(path_text).parent
            while parent != Path("."):
                expected_overlay_directories.add(parent.as_posix())
                parent = parent.parent
        if overlay_files != required_review_paths():
            raise IntegrationError(
                "reviewed-static overlay file set must equal the exact reviewed path set"
            )
        if overlay_directories != expected_overlay_directories:
            raise IntegrationError(
                "reviewed-static overlay directory set must be exact; "
                f"missing={sorted(expected_overlay_directories - overlay_directories)}, "
                f"extra={sorted(overlay_directories - expected_overlay_directories)}"
            )
        overlay_tree(overlay, stage)
        preserved_reviewed_source = (
            stage / "static" / "integration" / "reviewed-static-input"
        )
        copy_tree(overlay, preserved_reviewed_source)
        if reviewed_production_inputs:
            install_ready_reviewed_source_files(stage, preserved_reviewed_source)
        validate_hook_inventory(stage, expected_status="READY")
        validate_runtime_policy(stage, expected_status="READY")
        validate_reviewed_static(overlay, reviewed["reviewed_static"])

        reviewed_destination = stage / "static" / "integration" / "integration-values.json"
        write_exclusive(reviewed_destination, reviewed_bytes)
        write_exclusive(
            stage / "static" / "integration" / "source-declaration.json",
            declaration_bytes,
        )
        write_exclusive(stage / "static" / "generated" / "seeds.json", seeds_bytes)

        packages_document, targets_document, bindings = materialize_identities(
            stage, source_root, declaration, reviewed, inputs
        )
        write_json(stage / "packages.json", packages_document)
        write_json(stage / "targets.json", targets_document)
        write_json(stage / "static" / "integration" / "source-bindings.json", bindings)
        packages = prepare.validate_packages(packages_document)
        targets = prepare.validate_targets(targets_document)
        documents = prepare.generated_documents(packages, targets, seeds, status="READY")
        prepare.verify_generated(documents, seeds, expected_status="READY")
        for name, value in documents.items():
            write_json(stage / "static" / "generated" / name, value)
        generation_binding = {
            "schema_version": 1,
            "status": "READY",
            "source_declaration_sha256": sha256(declaration_bytes),
            "reviewed_values_sha256": sha256(reviewed_bytes),
            "seeds_sha256": sha256(seeds_bytes),
            "packages_sha256": sha256(pretty_json_bytes(packages_document)),
            "targets_sha256": sha256(pretty_json_bytes(targets_document)),
            "generated_sha256": {
                name: sha256(pretty_json_bytes(value)) for name, value in documents.items()
            },
        }
        write_json(
            stage / "static" / "generated" / "generation-binding.json", generation_binding
        )
        execution_digests, spec_digests = build_execution_and_envelope_specs(stage, reviewed)
        report_material = build_prompts_and_launches(
            stage,
            documents,
            packages,
            targets,
            reviewed,
            workspace_base,
            execution_digests,
            spec_digests,
        )
        source_digests = {
            mode: targets[mode]["byte_tree_sha256"] for mode in prepare.MODES
        }
        material_digests = mode_report_material_digests(
            report_material, documents
        )
        install_ready_fixture_manifests(
            stage,
            preserved_reviewed_source,
            source_digests=source_digests,
            material_digests=material_digests,
        )
        if production_declaration:
            validate_reviewed_semantic_closure(
                stage,
                expected_fixture_phase="READY",
                expected_source_digests=source_digests,
                expected_report_material_digests=material_digests,
                evidence_source_root=(
                    preserved_reviewed_inputs
                    / SOURCE_REVIEW_THEOREM_ROOT
                    / "unsafe-rust"
                ),
            )
        build_evaluator_material(stage, documents, execution_digests, spec_digests)
        write_json(
            stage / "static" / "integration" / "word-counter-binding.json",
            validate_word_counter(stage / "word_count.py"),
        )
        (stage / RUNTIME_STATE).mkdir(parents=True)
        install_snapshot_review_procedure(stage)
        build_snapshot_review_contracts(stage)
        create_review_snapshot(stage, bundle_kind=bundle_kind)
        verify_review_snapshot(stage, expected_candidate_kind=bundle_kind)
        publish_no_replace(stage, output)
    except Exception:
        if stage.exists():
            make_tree_writable(stage)
            shutil.rmtree(stage, ignore_errors=True)
        raise


def prepare_snapshot(
    *,
    source_root: Path,
    inputs: Path,
    output: Path,
    workspace_base: Path,
) -> None:
    _prepare_snapshot(
        source_root=source_root,
        inputs=inputs,
        output=output,
        workspace_base=workspace_base,
        declaration_path=SOURCE_DECLARATION,
        bundle_kind="PRODUCTION",
        synthetic_capability=None,
    )


def _finalize_snapshot(
    *,
    snapshot: Path,
    receipts: Path,
    output: Path,
    bundle_kind: str,
    synthetic_capability: object | None,
    external_commitment_output: Path | None = None,
) -> dict[str, Any]:
    if bundle_kind == "PRODUCTION":
        if synthetic_capability is not None:
            raise IntegrationError("synthetic path may not finalize PRODUCTION")
    elif bundle_kind == "SYNTHETIC-TEST-ONLY":
        if synthetic_capability is not _SYNTHETIC_CAPABILITY:
            raise IntegrationError("synthetic finalization is private to self-test")
    else:
        raise IntegrationError("unknown bundle kind")
    snapshot = snapshot.resolve()
    receipts = receipts.resolve()
    output = output.resolve()
    if external_commitment_output is not None:
        external_commitment_output = external_commitment_destination(
            output,
            external_commitment_output,
            "external commitment output",
        )
    protected_paths = [snapshot, receipts, output]
    if external_commitment_output is not None:
        protected_paths.append(external_commitment_output)
    if any(
        paths_overlap(first, second)
        for index, first in enumerate(protected_paths)
        for second in protected_paths[index + 1 :]
    ):
        raise IntegrationError("snapshot, receipts, and final output must be disjoint")
    if output.exists():
        raise IntegrationError(f"final output already exists: {output}")
    descriptor = verify_review_snapshot(
        snapshot, expected_candidate_kind=bundle_kind
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    fsync_directory(output.parent)
    stage = Path(tempfile.mkdtemp(prefix=".v5-final-stage-", dir=output.parent))
    try:
        stage.rmdir()
        copy_tree(snapshot, stage)
        staged_descriptor = verify_review_snapshot(
            stage, expected_candidate_kind=bundle_kind
        )
        if staged_descriptor != descriptor:
            raise IntegrationError("snapshot descriptor changed while copying for finalization")
        # The copied subject remains immutable through custody verification.
        # Only the verified private stage is then opened for finalization.
        make_tree_writable(stage)
        receipt_map = copy_snapshot_review_receipts(
            stage,
            stage,
            receipts,
            staged_descriptor,
            synthetic_capability=synthetic_capability,
        )
        creation_path = (
            "PRODUCTION_REVIEWED_SNAPSHOT_FINALIZATION"
            if bundle_kind == "PRODUCTION"
            else "PRIVATE_SYNTHETIC_SELF_TEST_FINALIZATION"
        )
        status = {
            "schema_version": 1,
            "status": "READY",
            "bundle_kind": bundle_kind,
            "creation_path": creation_path,
            "phase": "FINALIZE_STATIC_COMPLETE",
            "static_state": "BOUND_BY_ROOT_STATIC_LOCK",
            "semantic_launch_eligible": bundle_kind == "PRODUCTION",
            "semantic_launch_requires_expected_production_verification": True,
            "runtime_collection_receipts_required_after_lock": True,
            "postrun_aggregate_receipts_required_after_collection": True,
        }
        validate_schema_file(
            status,
            RUN / "schemas" / "integration-status.schema.json",
            "INTEGRATION-STATUS.json",
        )
        write_json(stage / "INTEGRATION-STATUS.json", status)
        create_manifest_and_lock(stage, receipt_map, bundle_kind=bundle_kind)
        _verify_static_precommit(
            stage,
            expected_bundle_kind=bundle_kind,
            capability=_FINALIZATION_PRECOMMIT_CAPABILITY,
        )
        commitment = _derive_external_static_commitment(stage)
        # The committed identity belongs to the verified private stage, not to
        # whatever entry happens to be visible at the destination afterward.
        _verify_static_precommit(
            stage,
            expected_bundle_kind=bundle_kind,
            capability=_FINALIZATION_PRECOMMIT_CAPABILITY,
        )
        if _derive_external_static_commitment(stage) != commitment:
            raise IntegrationError("final stage changed while deriving its commitment")
        publish_no_replace(stage, output)
        _verify_static_precommit(
            output,
            expected_bundle_kind=bundle_kind,
            capability=_FINALIZATION_PRECOMMIT_CAPABILITY,
        )
        if _derive_external_static_commitment(output) != commitment:
            raise IntegrationError(
                "published bundle is not the exact prepublication committed stage"
            )
        if external_commitment_output is not None:
            _publish_external_commitment_file(external_commitment_output, commitment)
        verify_static(
            output,
            expected_bundle_kind=bundle_kind,
            expected_external_commitment=commitment,
        )
        return commitment
    except Exception:
        if stage.exists():
            make_tree_writable(stage)
            shutil.rmtree(stage, ignore_errors=True)
        raise


def finalize_snapshot(
    *,
    snapshot: Path,
    receipts: Path,
    output: Path,
    external_commitment_output: Path,
) -> dict[str, Any]:
    return _finalize_snapshot(
        snapshot=snapshot,
        receipts=receipts,
        output=output,
        bundle_kind="PRODUCTION",
        synthetic_capability=None,
        external_commitment_output=external_commitment_output,
    )


def synthetic_execution_config() -> dict[str, Any]:
    return {
        role: {
            "model": "synthetic-model",
            "reasoning_effort": "synthetic",
            "sampling": "UNAVAILABLE_IN_SYNTHETIC_TEST",
            "token_budget": None,
            "token_budget_enforcement": "UNAVAILABLE_NOT_ENFORCED",
            "time_budget_seconds": None,
            "time_budget_enforcement": "UNAVAILABLE_NOT_ENFORCED",
            "requested_tools": ["read"],
            "tool_capability_observation": "SESSION_INHERITED_MAY_EXCEED_REQUEST",
            "tool_policy_enforcement": "PROMPT_ONLY_NOT_TECHNICALLY_ENFORCED",
            "requested_network_access": "DENIED",
            "network_capability_observation": "SESSION_INHERITED_MAY_EXCEED_REQUEST",
            "network_policy_enforcement": "PROMPT_ONLY_NOT_TECHNICALLY_ENFORCED",
            "requested_documentation_access": "MOUNTED_ONLY",
            "documentation_capability_observation": "SESSION_INHERITED_MAY_EXCEED_REQUEST",
            "documentation_policy_enforcement": "PROMPT_ONLY_NOT_TECHNICALLY_ENFORCED",
            "requested_hosted_build": "DISABLED",
            "hosted_build_capability_observation": "SESSION_INHERITED_MAY_EXCEED_REQUEST",
            "hosted_build_policy_enforcement": "PROMPT_ONLY_NOT_TECHNICALLY_ENFORCED",
        }
        for role in ROLE_NAMES
    }


def _build_mechanical_production_bundle_for_protocol_self_test(
    temporary_root: Path,
    *,
    synthetic_capability: object,
) -> tuple[Path, Path]:
    """Build a real PRODUCTION-shaped bundle for protocol regression tests.

    This private helper may only be called with this module's unforgeable
    synthetic capability.  It uses the public production receipt builders and
    finalizers, but its reviewer work products are mechanically generated test
    fixtures and therefore must never escape a temporary self-test directory.
    """

    if synthetic_capability is not _SYNTHETIC_CAPABILITY:
        raise IntegrationError("mechanical production test helper lacks its capability")
    temporary_root = absolute_normalized(
        temporary_root, "mechanical production protocol-test root"
    )
    if temporary_root.exists() or temporary_root.is_symlink():
        raise IntegrationError(
            f"mechanical production protocol-test root already exists: {temporary_root}"
        )
    temporary_root.mkdir(parents=True)
    declaration_bytes = trusted_production_declaration_bytes()
    inputs = temporary_root / "source-review-inputs"
    inputs.mkdir()
    reviewed = {
        "schema_version": 1,
        "status": "SOURCE-REVIEW-CANDIDATE",
        "source_declaration_sha256": sha256(declaration_bytes),
        "authority_packet_path": "docs/rust-documentation.json",
        "target_parameters": {
            mode: {"task_mode": "unsafe_rust_audit", "word_cap": 1000}
            for mode in prepare.MODES
        },
        "invocation_blocks": {
            "v5": "Use the selected current unsafe-Rust instruction package.",
            "v4": "Use the selected historical unsafe-Rust instruction package.",
            "no_skill": "",
        },
        "execution_environment": synthetic_execution_config(),
        "forbidden_tokens": ["no_skill", "no-skill", "treatment-secret"],
        "reviewed_static_base": REVIEWED_STATIC_DERIVED_BASE,
        "reviewed_static": [],
    }
    (inputs / "reviewed-values.json").write_bytes(pretty_json_bytes(reviewed))
    seeds = {
        name: sha256(f"protocol-staged-runtime-{name}".encode())
        for name in prepare.SEED_NAMES
    }
    (inputs / "seeds.json").write_bytes(pretty_json_bytes(seeds))

    source_candidate = temporary_root / "source-review-candidate"
    prepare_source_review(
        source_root=trusted_unsafe_rust_root(),
        inputs=inputs,
        output=source_candidate,
    )
    source_templates = temporary_root / "source-review-templates"
    write_synthetic_source_review_receipts(source_candidate, source_templates)
    source_receipts = temporary_root / "source-review-receipts"
    for index, (receipt_name, _review_kind) in enumerate(
        SOURCE_REVIEW_KINDS, start=1
    ):
        private_copy = temporary_root / f"source-private-{index}"
        prepare_source_review_copy(source_candidate, private_copy)
        template = read_json(source_templates / receipt_name)
        work_path = temporary_root / f"source-work-{index}.json"
        result_path = temporary_root / f"source-result-{index}.json"
        work_path.write_bytes(pretty_json_bytes(template["work_product"]))
        result_path.write_bytes(pretty_json_bytes(template["result"]))
        build_source_review_receipt(
            snapshot=source_candidate,
            private_copy=private_copy,
            review_name=receipt_name,
            actor_id=f"protocol-source-reviewer-{index:04d}",
            work_product_path=work_path,
            result_path=result_path,
            output=source_receipts / receipt_name,
        )
    reviewed_inputs = temporary_root / "reviewed-inputs"
    finalize_reviewed_inputs(
        snapshot=source_candidate,
        receipts=source_receipts,
        output=reviewed_inputs,
    )

    snapshot = temporary_root / "snapshot"
    prepare_snapshot(
        source_root=trusted_unsafe_rust_root(),
        inputs=reviewed_inputs,
        output=snapshot,
        workspace_base=Path("/tmp")
        / sha256(f"protocol-staged-runtime-{temporary_root}".encode()),
    )
    snapshot_templates = temporary_root / "snapshot-review-templates"
    write_synthetic_snapshot_receipts(
        snapshot, snapshot_templates, candidate_kind="PRODUCTION"
    )
    snapshot_receipts = temporary_root / "snapshot-review-receipts"
    for index, hook_id in enumerate(sorted(EXTERNAL_REVIEW_HOOKS), start=1):
        private_copy = temporary_root / f"snapshot-private-{index}"
        prepare_private_review_copy(snapshot, private_copy)
        template = read_json(snapshot_templates / f"{hook_id}.json")
        work_path = temporary_root / f"snapshot-work-{index}.json"
        result_path = temporary_root / f"snapshot-result-{index}.json"
        work_path.write_bytes(pretty_json_bytes(template["work_product"]))
        result_path.write_bytes(pretty_json_bytes(template["result"]))
        build_snapshot_review_receipt(
            snapshot=snapshot,
            private_copy=private_copy,
            hook_id=hook_id,
            actor_id=f"protocol-snapshot-reviewer-{index:04d}",
            work_product_path=work_path,
            result_path=result_path,
            output=snapshot_receipts / f"{hook_id}.json",
        )
    bundle = temporary_root / "bundle"
    commitment = temporary_root / "external-commitment.json"
    finalize_snapshot(
        snapshot=snapshot,
        receipts=snapshot_receipts,
        output=bundle,
        external_commitment_output=commitment,
    )
    return bundle, commitment


def synthetic_source_declaration(source_root: Path) -> dict[str, Any]:
    package_records: dict[str, Any] = {"no_skill": None}
    for role in ("v5", "v4"):
        provisional = source_root / f"package-{role}"
        provisional.mkdir(parents=True)
        (provisional / "SKILL.md").write_text(f"# Synthetic {role}\n", encoding="utf-8")
        (provisional / "notes.txt").write_text("synthetic package\n", encoding="utf-8")
        tree_sha = prepare.byte_tree_v1(provisional)
        final = source_root / tree_sha
        provisional.rename(final)
        package_records[role] = {
            "source_path": tree_sha,
            "skill_path": "SKILL.md",
            "directory_name_is_byte_tree_sha256": True,
        }
    target_records = []
    for mode in prepare.MODES:
        relative_path = f"targets/{mode.lower()}"
        target = source_root / relative_path
        target.mkdir(parents=True)
        (target / "REQUEST.md").write_text(
            f"Audit synthetic mode {mode} without treatment metadata.\n", encoding="utf-8"
        )
        (target / "lib.rs").write_text("pub unsafe fn example() {}\n", encoding="utf-8")
        target_records.append(
            {
                "mode": mode,
                "fixture_id": f"synthetic_{mode.lower()}",
                "source_path": relative_path,
                "prompt_regime": prepare.PROMPT_REGIMES[mode],
                "provenance": "SYNTHETIC_TEST_ONLY",
            }
        )
    return {
        "schema_version": 1,
        "status": "DRAFT-SOURCE-SELECTION",
        "byte_tree_algorithm": prepare.BYTE_TREE_ALGORITHM,
        "source_paths_relative_to": "unsafe-rust-root",
        "packages": package_records,
        "targets": target_records,
        "agent_visible_aliases": {
            "input": "input",
            "output": "output",
            "target": "target",
            "package": "package",
            "authority": "docs/rust-documentation.json",
        },
    }


def build_synthetic_reviewed_overlay(
    inputs: Path, source_root: Path, declaration: dict[str, Any]
) -> list[dict[str, Any]]:
    overlay = inputs / "reviewed-static"
    target_source_digests = {
        record["mode"]: prepare.byte_tree_v1(source_root / record["source_path"])
        for record in declaration["targets"]
    }
    files = derive_reviewed_static_files(
        target_source_digests=target_source_digests
    )
    for path_text, data in files.items():
        destination = overlay / path_text
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
    records = reviewed_static_records(files)
    validate_reviewed_static(overlay, records)
    return records


def write_synthetic_source_review_receipts(
    snapshot: Path, receipts: Path
) -> None:
    """Private self-test fixture; production has no receipt-minting helper."""

    descriptor = verify_source_review_snapshot(snapshot, require_receipts=False)
    contracts = validate_source_review_contracts(snapshot)
    descriptor_sha256 = sha256((snapshot / SOURCE_REVIEW_DESCRIPTOR).read_bytes())
    manifest_sha256 = sha256((snapshot / SOURCE_REVIEW_MANIFEST).read_bytes())
    receipts.mkdir()
    for index, (name, review_kind) in enumerate(SOURCE_REVIEW_KINDS, start=1):
        contract = contracts[name]
        contract_path = f"{SOURCE_REVIEW_CONTRACT_ROOT}/{name}"
        contract_sha256 = sha256((snapshot / contract_path).read_bytes())
        reviewer_runtime = current_reviewer_runtime_attestation()
        work_product = synthetic_review_work_product(
            contract["coverage_items"], label=contract["procedure_id"]
        )
        work_product_sha256 = review_work_product_sha256(work_product)
        generic_evidence = {
            "EXACT-SOURCE-REVIEW-BOUND": (
                f"Verified descriptor {descriptor_sha256} and exact payload "
                f"{descriptor['payload_manifest_sha256']}."
            ),
            "REVIEW-CONTRACT-BOUND": (
                f"Used contract {contract_sha256}, procedure "
                f"{contract['procedure_sha256']}, receipt schema "
                f"{contract['receipt_schema_sha256']}, under "
                f"{contract['procedure_version']}; reviewer tools "
                f"{contract['reviewer_tool_set_algorithm']} "
                f"{contract['reviewer_tool_set_sha256']}; coverage "
                f"{contract['coverage_set_algorithm']} "
                f"{contract['coverage_set_sha256']}; reviewer runtime "
                f"{reviewer_runtime['algorithm']}."
            ),
            "ARTIFACT-INVENTORY-CHECKED": (
                f"Checked every artifact in exact set {contract['artifact_set_sha256']}."
            ),
            "END-OF-REVIEW-REVERIFIED": (
                f"End reverified manifest {manifest_sha256} and payload "
                f"{descriptor['payload_manifest_sha256']}."
            ),
            "EXACT-QUOTATIONS-AND-PAGE-BYTES-VERIFIED": (
                "Verified every fetched official page byte hash and normalized excerpt "
                f"under {EXACT_QUOTATION_EVIDENCE_ALGORITHM}; evidence "
                f"{EXACT_QUOTATION_EVIDENCE_SHA256}."
            ),
            "ORACLE-ENTAILMENT-CHECKED": (
                "Checked every oracle proposition and atom entailment after exact "
                f"{SOURCE_REVIEW_TRANSITION_ALGORITHM} transformation against theorem "
                f"inputs {contract['evidence_bindings']['theorem_input_set_sha256']}."
            ),
            "AUTHORITY-PROJECTION-CHECKED": (
                "Checked the exact canonical authority projection within reviewed set "
                f"{contract['evidence_bindings']['reviewed_static_set_sha256']}."
            ),
            "CONTROL-AND-DEFECT-COVERAGE-CHECKED": (
                "Checked controls and defect coverage across exact reviewed set "
                f"{contract['evidence_bindings']['reviewed_static_set_sha256']}."
            ),
            "CROSS-FILE-CLOSURE-CHECKED": (
                "Checked all cross-file references under transformation contract "
                f"{SOURCE_REVIEW_TRANSITION_ALGORITHM}."
            ),
            "TRANSFORMATION-CORRECTNESS-CHECKED": (
                f"Checked {REVIEWED_STATIC_SET_ALGORITHM} exact transition output "
                f"{contract['evidence_bindings']['reviewed_static_set_sha256']} against "
                f"theorem inputs {contract['evidence_bindings']['theorem_input_set_sha256']}."
            ),
        }
        receipt = {
            "schema_version": 1,
            "status": "SYNTHETIC-TEST-ONLY",
            "review_kind": review_kind,
            "actor": {
                "identity": f"synthetic-source-reviewer-{index}",
                "role": "INDEPENDENT_REVIEWER",
                "implementation": contract["procedure_id"],
                "version": contract["procedure_version"],
            },
            "reviewer_runtime": reviewer_runtime,
            "input_digests": {
                SOURCE_REVIEW_DESCRIPTOR: descriptor_sha256,
                SOURCE_REVIEW_MANIFEST: manifest_sha256,
                contract_path: contract_sha256,
                contract["procedure_path"]: contract["procedure_sha256"],
                contract["receipt_schema_path"]: contract[
                    "receipt_schema_sha256"
                ],
                "trusted-reviewer-tool-set": contract[
                    "reviewer_tool_set_sha256"
                ],
                "reviewer-runtime-attestation": sha256(
                    canonical_json_bytes(reviewer_runtime)
                ),
            },
            "output_digests": {
                "reviewed-payload-manifest": descriptor["payload_manifest_sha256"],
                "reviewed-artifact-set": contract["artifact_set_sha256"],
                "review-work-product": work_product_sha256,
            },
            "work_product": work_product,
            "result": {
                "summary": "Synthetic self-test statement over the exact source-review contract.",
                "checks": [
                    {"id": check_id, "status": "PASS", "evidence": generic_evidence[check_id]}
                    for check_id in contract["required_check_ids"]
                ],
            },
        }
        (receipts / name).write_bytes(pretty_json_bytes(receipt))
    validate_source_review_receipts(
        receipts,
        snapshot_root=snapshot,
        descriptor_sha256=descriptor_sha256,
        manifest_sha256=manifest_sha256,
        payload_sha256=descriptor["payload_manifest_sha256"],
        synthetic_capability=_SYNTHETIC_CAPABILITY,
    )


def coherently_mutate_reviewed_exact_quote(
    reviewed_static_root: Path, old: str, new: str
) -> None:
    """Self-test helper which keeps all projection copies mutually consistent."""

    propositions_path = reviewed_static_root / "freeze/authority/propositions.json"
    locators_path = reviewed_static_root / "freeze/authority/quotation-locators.json"
    packet_path = reviewed_static_root / "freeze/authority/agent-visible/common.json"
    verification_path = reviewed_static_root / "freeze/authority/verification.json"
    propositions = read_json(propositions_path)
    locators = read_json(locators_path)
    packet = read_json(packet_path)
    replacements = 0
    for entry in propositions["entries"]:
        for key in ("quotation", "quotations"):
            if key not in entry:
                continue
            if key == "quotation" and entry[key] == old:
                entry[key] = new
                replacements += 1
            elif key == "quotations":
                replacements += sum(value == old for value in entry[key])
                entry[key] = [new if value == old else value for value in entry[key]]
    for record in locators["records"]:
        if record["exact_excerpt"] == old:
            record["exact_excerpt"] = new
    for record in packet["records"]:
        if record["exact_excerpt"] == old:
            record["exact_excerpt"] = new
    if replacements < 1:
        raise AssertionError("exact-quotation mutation sentinel found no proposition")
    propositions_path.write_bytes(pretty_json_bytes(propositions))
    locators_path.write_bytes(pretty_json_bytes(locators))
    packet_path.write_bytes(pretty_json_bytes(packet))
    verification = read_json(verification_path)
    verification["agent_visible_projection"]["sha256"] = sha256(packet_path.read_bytes())
    verification_path.write_bytes(pretty_json_bytes(verification))


def write_synthetic_snapshot_receipts(
    snapshot: Path,
    receipts: Path,
    *,
    candidate_kind: str = "SYNTHETIC-TEST-ONLY",
) -> None:
    descriptor = verify_review_snapshot(
        snapshot, expected_candidate_kind=candidate_kind
    )
    receipts.mkdir()
    for index, hook_id in enumerate(sorted(EXTERNAL_REVIEW_HOOKS), start=1):
        contract_path = f"static/integration/review-contracts/{hook_id}.json"
        contract = read_json(snapshot / contract_path)
        reviewer_runtime = current_reviewer_runtime_attestation()
        inputs = snapshot_receipt_inputs(
            snapshot,
            hook_id,
            reviewer_runtime=reviewer_runtime,
        )
        work_product = synthetic_review_work_product(
            contract["coverage_items"], label=contract["procedure_id"]
        )
        receipt = {
            "schema_version": 2,
            "status": "SYNTHETIC-TEST-ONLY",
            "phase": "SNAPSHOT_REVIEW",
            "hook_id": hook_id,
            "receipt_kind": "INDEPENDENT_SNAPSHOT_REVIEW",
            "actor": {
                "identity": f"synthetic-independent-reviewer-{index:02d}",
                "role": "INDEPENDENT_REVIEWER",
                "implementation": contract["procedure_id"],
                "version": contract["procedure_version"],
            },
            "reviewer_runtime": reviewer_runtime,
            "input_digests": inputs,
            "output_digests": {
                "reviewed-payload-manifest": descriptor["payload_manifest_sha256"],
                "reviewed-artifact-set": contract["artifact_set_sha256"],
                "review-work-product": review_work_product_sha256(work_product),
            },
            "work_product": work_product,
            "result": {
                "summary": f"Synthetic independent review passed the exact contract for {hook_id}.",
                "checks": [
                    {
                        "id": "EXACT-SNAPSHOT-BOUND",
                        "status": "PASS",
                        "evidence": (
                            "Verified descriptor "
                            f"{inputs[SNAPSHOT_DESCRIPTOR]} and payload manifest "
                            f"{descriptor['payload_manifest_sha256']} exactly."
                        ),
                    },
                    {
                        "id": "REVIEW-CONTRACT-BOUND",
                        "status": "PASS",
                        "evidence": (
                            f"Used locked {contract['procedure_version']} contract "
                            f"{inputs[contract_path]} and exact procedure "
                            f"{contract['procedure_sha256']} with receipt schema "
                            f"{contract['receipt_schema_sha256']}; coverage "
                            f"{contract['coverage_set_algorithm']} "
                            f"{contract['coverage_set_sha256']}; reviewer tools "
                            f"{contract['reviewer_tool_set_algorithm']} "
                            f"{contract['reviewer_tool_set_sha256']}; runtime "
                            f"{reviewer_runtime['algorithm']}."
                        ),
                    },
                    {
                        "id": "ARTIFACT-INVENTORY-CHECKED",
                        "status": "PASS",
                        "evidence": (
                            "Checked the complete exact artifact inventory "
                            f"{contract['artifact_set_sha256']}."
                        ),
                    },
                    {
                        "id": "HOOK-SEMANTICS-CHECKED",
                        "status": "PASS",
                        "evidence": (
                            f"Applied the recognized semantic procedure for {hook_id} "
                            "to every contracted artifact under acceptance set "
                            f"{contract['acceptance_requirements_sha256']}."
                        ),
                    },
                    {
                        "id": "END-OF-REVIEW-REVERIFIED",
                        "status": "PASS",
                        "evidence": (
                            "At review completion reverified framed manifest "
                            f"{inputs[SNAPSHOT_MANIFEST]} and payload "
                            f"{descriptor['payload_manifest_sha256']}."
                        ),
                    },
                ],
            },
        }
        receipt_path = receipts / f"{hook_id}.json"
        receipt_path.write_bytes(pretty_json_bytes(receipt))
        validate_snapshot_review_receipt(
            receipt_path,
            hook_id,
            snapshot,
            descriptor,
            synthetic_capability=_SYNTHETIC_CAPABILITY,
        )


def expect_integration_failure(operation: Callable[[], Any], message: str) -> None:
    try:
        operation()
    except IntegrationError:
        return
    raise AssertionError(message)


def self_test() -> None:
    draft()
    manifest_test_domain = b"ZEROCOPY\0V5\0SELF-TEST-MANIFEST\0V1"
    manifest_directory = framed_record(
        domain=manifest_test_domain,
        kind=b"D",
        path_bytes=b"a",
        size=0,
        content_sha256=b"\0" * 32,
        mode=0o555,
    )
    manifest_file = framed_record(
        domain=manifest_test_domain,
        kind=b"F",
        path_bytes=b"a/b.json",
        size=2,
        content_sha256=bytes.fromhex(sha256(b"{}")),
        mode=0o444,
    )
    manifest_prefix = manifest_test_domain + b"\0TREE\0"
    valid_manifest = (
        manifest_prefix
        + framed_u64(2)
        + manifest_directory
        + manifest_file
    )
    parsed_manifest = parse_tree_manifest_records(
        valid_manifest,
        domain=manifest_test_domain,
        include_mode=True,
        label="self-test framed manifest",
    )
    if parsed_manifest["a/b.json"] != {
        "kind": "F",
        "size": 2,
        "mode": 0o444,
        "content_sha256": sha256(b"{}"),
    }:
        raise AssertionError("framed-manifest parser changed an exact file record")
    duplicate_manifest = (
        manifest_prefix
        + framed_u64(2)
        + manifest_directory
        + manifest_directory
    )
    noncanonical_record = framed_record(
        domain=manifest_test_domain,
        kind=b"F",
        path_bytes=b"a/./b",
        size=0,
        content_sha256=bytes.fromhex(sha256(b"")),
        mode=0o444,
    )
    invalid_kind_record = framed_record(
        domain=manifest_test_domain,
        kind=b"X",
        path_bytes=b"x",
        size=0,
        content_sha256=bytes.fromhex(sha256(b"")),
        mode=0o444,
    )
    for malformed_manifest, description in (
        (valid_manifest[:-1], "truncated"),
        (valid_manifest + b"trailing", "trailing-byte"),
        (duplicate_manifest, "duplicate-path"),
        (
            manifest_prefix + framed_u64(1) + noncanonical_record,
            "noncanonical-path",
        ),
        (
            manifest_prefix + framed_u64(1) + invalid_kind_record,
            "invalid-kind",
        ),
    ):
        expect_integration_failure(
            lambda malformed_manifest=malformed_manifest: parse_tree_manifest_records(
                malformed_manifest,
                domain=manifest_test_domain,
                include_mode=True,
                label="malformed self-test framed manifest",
            ),
            f"framed-manifest parser accepted {description} input",
        )
    for invalid_actor_id in (
        "too-short",
        "Reviewer-alias-0001",
        "reviewer-unicode-é",
        "reviewer-control-\n0001",
    ):
        expect_integration_failure(
            lambda invalid_actor_id=invalid_actor_id: require_actor_id(
                invalid_actor_id, "synthetic invalid reviewer"
            ),
            f"reviewer identity grammar accepted {invalid_actor_id!r}",
        )
    forbidden_path_terms = read_json(RUN / "runtime-policy.json")[
        "agent_visible_path_forbidden_terms"
    ]
    for package_name in (
        "072a5c9d1b0000d04986f92a62ecc0ee2c7ff60c931c3fcd500128739c06c106",
        "6d7e197e431b82eb81dbe7eefc79fde811e0e238435d38c69460cc068e631abb",
    ):
        historical_package = RUN.parent.parent / "frozen-packages" / package_name
        if historical_package.is_dir() and prepare.byte_tree_v1(historical_package) != package_name:
            raise AssertionError(
                f"BYTE_TREE_V1 does not reproduce frozen package identity {package_name}"
            )
    for bad in (b'{"x":1,"x":2}', b'{"x":NaN}', b'\xff'):
        expect_integration_failure(
            lambda bad=bad: parse_json_bytes(bad, "synthetic-invalid"),
            "strict JSON parser accepted invalid input",
        )
    with tempfile.TemporaryDirectory(
        prefix="opaque-static-self-test-",
        dir=neutral_self_test_parent(forbidden_path_terms),
    ) as directory:
        temp = Path(directory)
        receipt_predicate_path = temp / "receipt-predicate.json"
        predicate_value = {"schema_version": 1, "status": "PASS"}
        receipt_predicate_path.write_bytes(canonical_json_bytes(predicate_value))
        os.chmod(receipt_predicate_path, 0o444)
        if read_canonical_read_only_json(
            receipt_predicate_path, "synthetic canonical receipt"
        )[0] != predicate_value:
            raise AssertionError("canonical read-only receipt predicate changed its value")
        # The production reader must authenticate the opened inode, not metadata
        # obtained from a pathname before a second open. Spoofing every Path.lstat
        # result as the known-good file therefore cannot hide a writable inode or
        # make a symlink acceptable.
        writable_race_path = temp / "receipt-writable-lstat-race.json"
        writable_race_path.write_bytes(canonical_json_bytes(predicate_value))
        symlink_target = temp / "receipt-symlink-target.json"
        symlink_target.write_bytes(canonical_json_bytes(predicate_value))
        os.chmod(symlink_target, 0o444)
        symlink_race_path = temp / "receipt-symlink-lstat-race.json"
        symlink_race_path.symlink_to(symlink_target)
        real_path_lstat = Path.lstat
        known_good_info = receipt_predicate_path.lstat()

        def spoof_receipt_lstat(path: Path) -> os.stat_result:
            if path in {writable_race_path, symlink_race_path}:
                return known_good_info
            return real_path_lstat(path)

        Path.lstat = spoof_receipt_lstat
        try:
            for race_path, reason in (
                (writable_race_path, "read-only"),
                (symlink_race_path, "securely open/read"),
            ):
                try:
                    read_canonical_read_only_json(
                        race_path, f"synthetic lstat-substitution {race_path.name}"
                    )
                except IntegrationError as error:
                    if reason not in str(error):
                        raise AssertionError(
                            "receipt lstat-substitution rejection had the wrong reason"
                        ) from error
                else:
                    raise AssertionError(
                        "production receipt reader trusted spoofed pathname metadata"
                    )
        finally:
            Path.lstat = real_path_lstat
        # Replace the pathname after os.open but before the first descriptor
        # metadata check. The callback must fire, the path must become valid B,
        # and the successful capture must still be the already-opened valid A.
        inode_race_path = temp / "receipt-open-inode-race.json"
        inode_a_value = {"schema_version": 1, "status": "PASS", "value": "A"}
        inode_b_value = {"schema_version": 1, "status": "PASS", "value": "B"}
        inode_a_bytes = canonical_json_bytes(inode_a_value)
        inode_b_bytes = canonical_json_bytes(inode_b_value)
        inode_race_path.write_bytes(inode_a_bytes)
        os.chmod(inode_race_path, 0o444)
        inode_b_stage = temp / "receipt-open-inode-race-B.json"
        inode_b_stage.write_bytes(inode_b_bytes)
        os.chmod(inode_b_stage, 0o444)
        real_os_fstat = os.fstat
        inode_substitution_fired = False

        def substitute_path_before_first_fstat(
            descriptor: int,
        ) -> os.stat_result:
            nonlocal inode_substitution_fired
            if not inode_substitution_fired:
                os.replace(inode_b_stage, inode_race_path)
                inode_substitution_fired = True
            return real_os_fstat(descriptor)

        os.fstat = substitute_path_before_first_fstat
        try:
            captured_inode_value, captured_inode_bytes = (
                read_canonical_read_only_json(
                    inode_race_path, "synthetic opened-inode substitution"
                )
            )
        finally:
            os.fstat = real_os_fstat
        if (
            not inode_substitution_fired
            or inode_race_path.read_bytes() != inode_b_bytes
            or captured_inode_value != inode_a_value
            or captured_inode_bytes != inode_a_bytes
        ):
            raise AssertionError(
                "production receipt capture followed a substituted pathname after open"
            )
        os.chmod(receipt_predicate_path, 0o644)
        expect_integration_failure(
            lambda: read_canonical_read_only_json(
                receipt_predicate_path, "synthetic writable receipt"
            ),
            "production receipt predicate accepted writable bytes",
        )
        receipt_predicate_path.write_bytes(pretty_json_bytes(predicate_value))
        os.chmod(receipt_predicate_path, 0o444)
        expect_integration_failure(
            lambda: read_canonical_read_only_json(
                receipt_predicate_path, "synthetic noncanonical receipt"
            ),
            "production receipt predicate accepted noncanonical JSON",
        )
        staged_counter = temp / "staged-word-count.py"
        staged_counter.write_bytes((RUN / "word_count.py").read_bytes())
        counter_sentinel = temp / "candidate-word-counter-executed"
        replacement_counter = temp / "candidate-word-counter-replacement.py"
        replacement_counter.write_text(
            "from pathlib import Path\n"
            f"Path({str(counter_sentinel)!r}).write_text('executed')\n"
            "ALGORITHM_ID = 'malicious-candidate-counter'\n"
            "def count_words(data): return 0\n",
            encoding="utf-8",
        )
        real_file_capture = globals()["capture_regular_file_bytes"]
        counter_substitution_fired = False

        def substitute_counter_after_capture(
            path: Path, label: str, *, require_read_only: bool
        ) -> bytes:
            nonlocal counter_substitution_fired
            data = real_file_capture(
                path, label, require_read_only=require_read_only
            )
            if path == staged_counter and not counter_substitution_fired:
                os.replace(replacement_counter, staged_counter)
                counter_substitution_fired = True
            return data

        globals()["capture_regular_file_bytes"] = substitute_counter_after_capture
        try:
            expect_integration_failure(
                lambda: validate_word_counter(staged_counter),
                "staged word-counter substitution escaped the final capture check",
            )
        finally:
            globals()["capture_regular_file_bytes"] = real_file_capture
        if not counter_substitution_fired or counter_sentinel.exists():
            raise AssertionError(
                "candidate word-counter bytes were not captured without execution"
            )
        direct_cli_root = temp / "direct-cli-no-bytecode"
        direct_cli_root.mkdir()
        direct_integrator = direct_cli_root / "integrate.py"
        shutil.copy2(RUN / "integrate.py", direct_integrator)
        shutil.copy2(RUN / "prepare.py", direct_cli_root / "prepare.py")
        os.chmod(direct_integrator, 0o755)
        direct_runtime = subprocess.run(
            [str(direct_integrator), "reviewer-runtime-attestation"],
            cwd=direct_cli_root,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if (
            parse_json_bytes(direct_runtime.stdout, "direct CLI runtime")
            != current_reviewer_runtime_attestation()
            or list(direct_cli_root.rglob("__pycache__"))
            or list(direct_cli_root.rglob("*.pyc"))
        ):
            raise AssertionError("direct CLI invocation created Python cache artifacts")
        interrupted_commitment = temp / "interrupted-external-commitment.json"
        interrupted_stage: Path | None = None
        real_publish_no_replace = publish_no_replace

        def interrupt_commitment_publication(stage: Path, output: Path) -> None:
            nonlocal interrupted_stage
            interrupted_stage = stage
            if output != interrupted_commitment:
                raise AssertionError("fault injection intercepted the wrong publication")
            if (
                stage.read_bytes() != canonical_json_bytes({"synthetic": "commitment"})
                or stat.S_IMODE(stage.stat(follow_symlinks=False).st_mode) != 0o444
            ):
                raise AssertionError(
                    "external commitment was not complete, fsynced, and read-only before publication"
                )
            if os.path.lexists(output):
                raise AssertionError("final commitment path existed before atomic publication")
            raise IntegrationError("synthetic interruption before no-replace publication")

        globals()["publish_no_replace"] = interrupt_commitment_publication
        try:
            expect_integration_failure(
                lambda: _publish_external_commitment_file(
                    interrupted_commitment, {"synthetic": "commitment"}
                ),
                "interrupted commitment publication unexpectedly succeeded",
            )
        finally:
            globals()["publish_no_replace"] = real_publish_no_replace
        if (
            os.path.lexists(interrupted_commitment)
            or interrupted_stage is None
            or os.path.lexists(interrupted_stage)
        ):
            raise AssertionError(
                "interrupted commitment publication left a final or handled-stage artifact"
            )

        source_root = temp / "sources"
        source_root.mkdir()
        declaration = synthetic_source_declaration(source_root)
        declaration_path = temp / "source-declaration.json"
        declaration_bytes = pretty_json_bytes(declaration)
        declaration_path.write_bytes(declaration_bytes)
        inputs = temp / "inputs"
        inputs.mkdir()
        (inputs / "authority.json").write_text(
            '{"synthetic":"neutral authority"}\n', encoding="utf-8"
        )
        reviewed_static = build_synthetic_reviewed_overlay(
            inputs, source_root, declaration
        )
        reviewed = {
            "schema_version": 1,
            "status": "READY",
            "source_declaration_sha256": sha256(declaration_bytes),
            "authority_packet_path": "authority.json",
            "target_parameters": {
                mode: {"task_mode": "synthetic_test_only", "word_cap": 1000}
                for mode in prepare.MODES
            },
            "invocation_blocks": {
                "v5": "Follow the first synthetic instruction package.",
                "v4": "Follow the second synthetic instruction package.",
                "no_skill": "",
            },
            "execution_environment": synthetic_execution_config(),
            "forbidden_tokens": ["no_skill", "no-skill", "treatment-secret"],
            "reviewed_static_base": REVIEWED_STATIC_CANDIDATE_BASE,
            "reviewed_static": reviewed_static,
        }
        (inputs / "reviewed-values.json").write_bytes(pretty_json_bytes(reviewed))
        seeds = {
            name: sha256(f"synthetic-integration-{name}".encode())
            for name in prepare.SEED_NAMES
        }
        (inputs / "seeds.json").write_bytes(pretty_json_bytes(seeds))
        workspace_base = Path("/tmp") / sha256(str(temp).encode())
        forbidden_workspace = Path("/tmp") / ("0" * 56 + "no_skill")
        expect_integration_failure(
            lambda: require_neutral_workspace_base(forbidden_workspace, forbidden_path_terms),
            "workspace path neutrality accepted a forbidden/nonopaque leaf",
        )
        expect_integration_failure(
            lambda: _prepare_snapshot(
                source_root=source_root,
                inputs=inputs,
                output=temp / "forbidden-production-snapshot",
                workspace_base=workspace_base,
                declaration_path=declaration_path,
                bundle_kind="PRODUCTION",
                synthetic_capability=None,
            ),
            "synthetic source path prepared a production review candidate",
        )
        snapshot = temp / "review-snapshot"
        _prepare_snapshot(
            source_root=source_root,
            inputs=inputs,
            output=snapshot,
            workspace_base=workspace_base,
            declaration_path=declaration_path,
            bundle_kind="SYNTHETIC-TEST-ONLY",
            synthetic_capability=_SYNTHETIC_CAPABILITY,
        )
        verify_review_snapshot(snapshot, expected_candidate_kind="SYNTHETIC-TEST-ONLY")
        for filename, version_field in (
            ("root-inventory.json", "inventory_version"),
            ("gate-manifest.json", "manifest_version"),
        ):
            operational_version_forgery = (
                temp / f"operational-version-forgery-{filename.removesuffix('.json')}"
            )
            copy_tree(snapshot, operational_version_forgery)
            make_tree_writable(operational_version_forgery)
            operational_path = operational_version_forgery / filename
            operational_value = read_json(operational_path)
            operational_value[version_field] = (
                "v5-diagnostic-prequalification-draft-1"
            )
            operational_path.write_bytes(pretty_json_bytes(operational_value))
            expect_integration_failure(
                lambda operational_version_forgery=operational_version_forgery: validate_snapshot_build_products(
                    operational_version_forgery,
                    bundle_kind="SYNTHETIC-TEST-ONLY",
                ),
                f"snapshot validation accepted READY/draft version drift: {filename}",
            )
        evaluator_contract = read_json(
            snapshot / "static" / "generated" / "evaluator-launch-contracts.json"
        )
        if len(evaluator_contract["assignments"]) != 43:
            raise AssertionError("snapshot did not freeze all 43 evaluator assignments")

        stateful_snapshot = temp / "stateful-review-snapshot"
        copy_tree(snapshot, stateful_snapshot)
        make_tree_writable(stateful_snapshot)
        (stateful_snapshot / RUNTIME_STATE / "pre-lock.json").write_text(
            '{"forged":"before-lock"}\n', encoding="utf-8"
        )
        expect_integration_failure(
            lambda: verify_review_snapshot(
                stateful_snapshot,
                expected_candidate_kind="SYNTHETIC-TEST-ONLY",
            ),
            "review verification accepted nonempty pre-lock runtime/state",
        )

        evaluator_forgery = temp / "evaluator-forgery"
        copy_tree(snapshot, evaluator_forgery)
        make_tree_writable(evaluator_forgery)
        forged_contract_path = (
            evaluator_forgery
            / "static"
            / "generated"
            / "evaluator-launch-contracts.json"
        )
        forged_contract = read_json(forged_contract_path)
        forged_record = forged_contract["assignments"][0]
        forged_prompt_path = evaluator_forgery / forged_record["prompt_path"]
        forged_prompt_path.write_bytes(forged_prompt_path.read_bytes() + b"\nforged\n")
        forged_record["prompt_sha256"] = sha256(forged_prompt_path.read_bytes())
        forged_contract_path.write_bytes(pretty_json_bytes(forged_contract))
        forged_receipt_path = (
            evaluator_forgery
            / "static"
            / "generated"
            / "evaluator-prompt-validation-receipt.json"
        )
        forged_receipt = read_json(forged_receipt_path)
        forged_receipt["assignment_prompt_sha256"][forged_record["assignment_id"]] = (
            forged_record["prompt_sha256"]
        )
        forged_receipt_path.write_bytes(pretty_json_bytes(forged_receipt))
        shutil.rmtree(
            evaluator_forgery / "static" / "integration" / "review-contracts"
        )
        (evaluator_forgery / SNAPSHOT_DESCRIPTOR).unlink()
        (evaluator_forgery / SNAPSHOT_MANIFEST).unlink()
        build_snapshot_review_contracts(evaluator_forgery)
        create_review_snapshot(
            evaluator_forgery, bundle_kind="SYNTHETIC-TEST-ONLY"
        )
        expect_integration_failure(
            lambda: verify_review_snapshot(
                evaluator_forgery,
                expected_candidate_kind="SYNTHETIC-TEST-ONLY",
            ),
            "verifier accepted coherently self-described forged evaluator bytes",
        )

        mount_forgery = temp / "coherent-report-mount-forgery"
        copy_tree(snapshot, mount_forgery)
        make_tree_writable(mount_forgery)
        forged_targets = prepare.validate_targets(read_json(mount_forgery / "targets.json"))
        forged_packages = prepare.validate_packages(read_json(mount_forgery / "packages.json"))
        generated_root = mount_forgery / "static" / "generated"
        changed_launches: dict[str, dict[str, Any]] = {}

        target_run = "r001"
        target_launch_path = generated_root / "launch-records" / f"{target_run}.json"
        target_plan_path = generated_root / "report-input-plans" / f"{target_run}.json"
        target_launch = read_json(target_launch_path)
        if target_launch["mode"] != "F":
            raise AssertionError("coherent-forgery sentinel expects r001 to be mode F")
        target_plan = read_json(target_plan_path)
        target_entry = next(
            item for item in target_plan["entries"] if item["destination"] == "input/target"
        )
        target_entry["source_path"] = forged_targets["E"]["source_path"]
        target_entry["sha256"] = forged_targets["E"]["byte_tree_sha256"]
        target_plan_path.write_bytes(pretty_json_bytes(target_plan))
        target_launch["target_byte_tree_sha256"] = forged_targets["E"][
            "byte_tree_sha256"
        ]
        target_launch["input_packet_sha256"] = sha256(target_plan_path.read_bytes())
        target_launch_path.write_bytes(pretty_json_bytes(target_launch))
        changed_launches[target_run] = target_launch

        package_run = "r002"
        package_launch_path = generated_root / "launch-records" / f"{package_run}.json"
        package_plan_path = generated_root / "report-input-plans" / f"{package_run}.json"
        package_launch = read_json(package_launch_path)
        if package_launch["condition_role"] != "v5":
            raise AssertionError("coherent-forgery sentinel expects r002 to be V5")
        package_plan = read_json(package_plan_path)
        package_entry = next(
            item
            for item in package_plan["entries"]
            if item["destination"] == "input/package"
        )
        package_entry["source_path"] = forged_packages["v4"]["source_path"]
        package_entry["sha256"] = forged_packages["v4"]["byte_tree_sha256"]
        package_plan_path.write_bytes(pretty_json_bytes(package_plan))
        package_launch["package_byte_tree_sha256"] = forged_packages["v4"][
            "byte_tree_sha256"
        ]
        package_launch["input_packet_sha256"] = sha256(package_plan_path.read_bytes())
        package_launch_path.write_bytes(pretty_json_bytes(package_launch))
        changed_launches[package_run] = package_launch

        prompt_receipt_path = generated_root / "prompt-validation-receipt.json"
        prompt_receipt = read_json(prompt_receipt_path)
        for run_id in changed_launches:
            prompt_receipt["launch_record_sha256"][run_id] = sha256(
                (generated_root / "launch-records" / f"{run_id}.json").read_bytes()
            )
        prompt_receipt_path.write_bytes(pretty_json_bytes(prompt_receipt))
        shutil.rmtree(mount_forgery / "static" / "integration" / "review-contracts")
        (mount_forgery / SNAPSHOT_DESCRIPTOR).unlink()
        (mount_forgery / SNAPSHOT_MANIFEST).unlink()
        build_snapshot_review_contracts(mount_forgery)
        create_review_snapshot(
            mount_forgery, bundle_kind="SYNTHETIC-TEST-ONLY"
        )
        expect_integration_failure(
            lambda: verify_review_snapshot(
                mount_forgery,
                expected_candidate_kind="SYNTHETIC-TEST-ONLY",
            ),
            "verifier accepted coherent F-to-E target and V5-to-V4 package substitutions",
        )

        wrong_package_forgery = temp / "wrong-package-production-forgery"
        copy_tree(snapshot, wrong_package_forgery)
        make_tree_writable(wrong_package_forgery)
        trusted_declaration_bytes = trusted_production_declaration_bytes()
        embedded_declaration_path = (
            wrong_package_forgery
            / "static"
            / "integration"
            / "source-declaration.json"
        )
        embedded_declaration_path.write_bytes(trusted_declaration_bytes)
        forged_values_path = (
            wrong_package_forgery / "static" / "integration" / "integration-values.json"
        )
        forged_values = read_json(forged_values_path)
        forged_values["source_declaration_sha256"] = sha256(trusted_declaration_bytes)
        forged_values_path.write_bytes(pretty_json_bytes(forged_values))
        forged_binding_path = (
            wrong_package_forgery / "static" / "integration" / "source-bindings.json"
        )
        forged_binding = read_json(forged_binding_path)
        forged_binding["source_declaration_sha256"] = sha256(trusted_declaration_bytes)
        forged_binding_path.write_bytes(pretty_json_bytes(forged_binding))
        forged_generation_path = (
            wrong_package_forgery / "static" / "generated" / "generation-binding.json"
        )
        forged_generation = read_json(forged_generation_path)
        forged_generation["source_declaration_sha256"] = sha256(
            trusted_declaration_bytes
        )
        forged_generation["reviewed_values_sha256"] = sha256(
            forged_values_path.read_bytes()
        )
        forged_generation_path.write_bytes(pretty_json_bytes(forged_generation))
        shutil.rmtree(
            wrong_package_forgery / "static" / "integration" / "review-contracts"
        )
        (wrong_package_forgery / SNAPSHOT_DESCRIPTOR).unlink()
        (wrong_package_forgery / SNAPSHOT_MANIFEST).unlink()
        build_snapshot_review_contracts(wrong_package_forgery)
        create_review_snapshot(wrong_package_forgery, bundle_kind="PRODUCTION")
        expect_integration_failure(
            lambda: verify_review_snapshot(
                wrong_package_forgery, expected_candidate_kind="PRODUCTION"
            ),
            "PRODUCTION verification trusted coherent candidate package self-description",
        )
        receipts = temp / "receipts"
        write_synthetic_snapshot_receipts(snapshot, receipts)
        expect_integration_failure(
            lambda: _finalize_snapshot(
                snapshot=stateful_snapshot,
                receipts=receipts,
                output=temp / "stateful-final",
                bundle_kind="SYNTHETIC-TEST-ONLY",
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "finalizer accepted nonempty runtime/state before STATIC-LOCK",
        )

        first_hook = sorted(EXTERNAL_REVIEW_HOOKS)[0]
        stale_receipt = read_json(receipts / f"{first_hook}.json")
        stale_receipt["input_digests"][SNAPSHOT_MANIFEST] = "0" * 64
        stale_path = temp / "stale-receipt.json"
        stale_path.write_bytes(pretty_json_bytes(stale_receipt))
        expect_integration_failure(
            lambda: validate_snapshot_review_receipt(
                stale_path,
                first_hook,
                snapshot,
                read_json(snapshot / SNAPSHOT_DESCRIPTOR),
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "snapshot review accepted a stale snapshot digest",
        )
        incomplete = read_json(receipts / f"{first_hook}.json")
        incomplete["actor"]["version"] = ""
        expect_integration_failure(
            lambda: validate_integration_receipt(
                incomplete,
                expected_hook_id=first_hook,
                expected_phase="SNAPSHOT_REVIEW",
            ),
            "receipt validator accepted an unversioned reviewer",
        )
        wrong_procedure = read_json(receipts / f"{first_hook}.json")
        wrong_procedure["actor"]["implementation"] = "unrecognized-review-procedure"
        wrong_procedure_path = temp / "wrong-procedure-receipt.json"
        wrong_procedure_path.write_bytes(pretty_json_bytes(wrong_procedure))
        expect_integration_failure(
            lambda: validate_snapshot_review_receipt(
                wrong_procedure_path,
                first_hook,
                snapshot,
                read_json(snapshot / SNAPSHOT_DESCRIPTOR),
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "snapshot review accepted an unrecognized procedure",
        )

        mutated_snapshot = temp / "mutated-snapshot"
        copy_tree(snapshot, mutated_snapshot)
        make_tree_writable(mutated_snapshot)
        mutation_target = next(
            (mutated_snapshot / "static" / "generated" / "report-prompts").glob("*.md")
        )
        mutation_target.write_bytes(mutation_target.read_bytes() + b"mutation")
        expect_integration_failure(
            lambda: _finalize_snapshot(
                snapshot=mutated_snapshot,
                receipts=receipts,
                output=temp / "mutated-final",
                bundle_kind="SYNTHETIC-TEST-ONLY",
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "finalizer accepted a snapshot changed after review commitment",
        )
        expect_integration_failure(
            lambda: _finalize_snapshot(
                snapshot=snapshot,
                receipts=receipts,
                output=temp / "forbidden-production",
                bundle_kind="PRODUCTION",
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "synthetic capability minted a production bundle",
        )

        output = temp / "bundle"
        commitment = _finalize_snapshot(
            snapshot=snapshot,
            receipts=receipts,
            output=output,
            bundle_kind="SYNTHETIC-TEST-ONLY",
            synthetic_capability=_SYNTHETIC_CAPABILITY,
        )
        verify_static(
            output,
            expected_bundle_kind="SYNTHETIC-TEST-ONLY",
            expected_external_commitment=commitment,
        )
        expect_integration_failure(
            lambda: _verify_static_precommit(
                output,
                expected_bundle_kind="SYNTHETIC-TEST-ONLY",
                capability=object(),
            ),
            "private precommit verifier accepted an unrecognized capability",
        )
        forged_commitment = {**commitment, "static_lock_sha256": "0" * 64}
        expect_integration_failure(
            lambda: verify_static(
                output,
                expected_bundle_kind="SYNTHETIC-TEST-ONLY",
                expected_external_commitment=forged_commitment,
            ),
            "verify-static accepted a wrong external whole-bundle commitment",
        )
        expect_integration_failure(
            lambda: verify_static(
                output,
                expected_bundle_kind="PRODUCTION",
                expected_external_commitment=commitment,
            ),
            "production verifier accepted a synthetic bundle",
        )
        prompts = sorted((output / "static" / "generated" / "report-prompts").glob("*.md"))
        launches = sorted((output / "static" / "generated" / "launch-records").glob("*.json"))
        if len(prompts) != 120 or len(launches) != 120:
            raise AssertionError("synthetic integration did not render 120 prompts/launches")
        if any(str(workspace_base).encode() in path.read_bytes() for path in prompts):
            raise AssertionError("an absolute workspace path leaked into a report prompt")
        first_plan = read_json(
            output / "static" / "generated" / "report-input-plans" / "r001.json"
        )
        schema_entries = [
            entry for entry in first_plan["entries"] if entry["destination"].startswith("input/schemas/")
        ]
        first_launch = read_json(
            output / "static" / "generated" / "launch-records" / "r001.json"
        )
        expected_destinations = {"input/target", "input/docs/rust-documentation.json"}
        if first_launch["condition_role"] != "no_skill":
            expected_destinations.add("input/package")
        if (
            schema_entries != []
            or first_launch["schema_paths"] != []
            or {entry["destination"] for entry in first_plan["entries"]}
            != expected_destinations
        ):
            raise AssertionError("report agent received an inexact visible mount set")

        source_review_inputs = temp / "source-review-inputs"
        source_review_inputs.mkdir()
        production_declaration_bytes = trusted_production_declaration_bytes()
        production_reviewed = {
            "schema_version": 1,
            "status": "SOURCE-REVIEW-CANDIDATE",
            "source_declaration_sha256": sha256(production_declaration_bytes),
            "authority_packet_path": "docs/rust-documentation.json",
            "target_parameters": {
                mode: {"task_mode": "unsafe_rust_audit", "word_cap": 1000}
                for mode in prepare.MODES
            },
            "invocation_blocks": {
                "v5": "Use the selected current unsafe-Rust instruction package.",
                "v4": "Use the selected historical unsafe-Rust instruction package.",
                "no_skill": "",
            },
            "execution_environment": synthetic_execution_config(),
            "forbidden_tokens": ["no_skill", "no-skill", "treatment-secret"],
            "reviewed_static_base": REVIEWED_STATIC_DERIVED_BASE,
            "reviewed_static": [],
        }
        (source_review_inputs / "reviewed-values.json").write_bytes(
            pretty_json_bytes(production_reviewed)
        )
        (source_review_inputs / "seeds.json").write_bytes(pretty_json_bytes(seeds))
        source_review_candidate = temp / "source-review-candidate"
        prepare_source_review(
            source_root=trusted_unsafe_rust_root(),
            inputs=source_review_inputs,
            output=source_review_candidate,
        )
        reviewer_tool_mirror = temp / "reviewer-tool-mirror"
        for record in source_review_tool_records(RUN):
            write_exclusive(
                reviewer_tool_mirror / record["path"],
                (RUN / record["path"]).read_bytes(),
            )
        validate_source_review_contracts(
            source_review_candidate, tool_root=reviewer_tool_mirror
        )
        mirrored_integrator = reviewer_tool_mirror / "integrate.py"
        mirrored_integrator.write_bytes(
            mirrored_integrator.read_bytes() + b"\n# substituted reviewer tool\n"
        )
        expect_integration_failure(
            lambda: validate_source_review_contracts(
                source_review_candidate, tool_root=reviewer_tool_mirror
            ),
            "source-review contract accepted substituted reviewer-tool bytes",
        )
        production_declaration = validate_source_declaration(
            parse_json_bytes(
                production_declaration_bytes, "self-test production declaration"
            ),
            production=True,
        )
        production_source_digests = trusted_target_source_digests(
            production_declaration
        )
        for mutation_name, old_quote, new_quote in (
            (
                "p-comma",
                "Returns the contained `Some` value, consuming the `self` value, without checking that the value is not `None`.",
                "Returns the contained `Some` value, consuming the `self` value without checking that the value is not `None`.",
            ),
            ("equality-premise", "`==` Equal", "`==` Comparison"),
        ):
            quotation_forgery = temp / f"source-quotation-forgery-{mutation_name}"
            copy_tree(source_review_candidate, quotation_forgery)
            make_tree_writable(quotation_forgery)
            coherently_mutate_reviewed_exact_quote(
                quotation_forgery / "reviewed-static", old_quote, new_quote
            )
            expect_integration_failure(
                lambda quotation_forgery=quotation_forgery: validate_reviewed_semantic_closure(
                    quotation_forgery / "reviewed-static",
                    expected_fixture_phase="SOURCE_REVIEW_CANDIDATE",
                    expected_source_digests=production_source_digests,
                    evidence_source_root=(
                        quotation_forgery
                        / SOURCE_REVIEW_THEOREM_ROOT
                        / "unsafe-rust"
                    ),
                ),
                f"semantic closure accepted coherent exact-quotation drift: {mutation_name}",
            )

        lineage_overclaim = temp / "source-lineage-overclaim-forgery"
        copy_tree(source_review_candidate, lineage_overclaim)
        make_tree_writable(lineage_overclaim)
        lineage_verification_path = (
            lineage_overclaim
            / "reviewed-static/freeze/authority/verification.json"
        )
        lineage_verification = read_json(lineage_verification_path)
        lineage_verification["versioned_page_byte_lineage"]["coverage_basis"] = (
            "The V4 reviews prove every current V5 quotation and proposition."
        )
        lineage_verification_path.write_bytes(
            pretty_json_bytes(lineage_verification)
        )
        expect_integration_failure(
            lambda: validate_reviewed_semantic_closure(
                lineage_overclaim / "reviewed-static",
                expected_fixture_phase="SOURCE_REVIEW_CANDIDATE",
                expected_source_digests=production_source_digests,
                evidence_source_root=(
                    lineage_overclaim
                    / SOURCE_REVIEW_THEOREM_ROOT
                    / "unsafe-rust"
                ),
            ),
            "semantic closure accepted a false V4-to-V5 authority-lineage overclaim",
        )

        projection_ledger_forgery = temp / "source-projection-ledger-forgery"
        copy_tree(source_review_candidate, projection_ledger_forgery)
        make_tree_writable(projection_ledger_forgery)
        projection_authority_root = (
            projection_ledger_forgery / "reviewed-static/freeze/authority"
        )
        projection_verification_path = projection_authority_root / "verification.json"
        projection_propositions_path = projection_authority_root / "propositions.json"
        base_projection_verification = read_json(projection_verification_path)
        base_projection_propositions = read_json(projection_propositions_path)
        validate_projection = runpy.run_path(
            str(RUN / "freeze" / "authority" / "validate_agent_visible.py"),
            run_name="v5_integration_projection_ledger_mutation",
        )["validate"]

        def reject_projection_ledger_mutation(
            label: str,
            verification_value: dict[str, Any],
            propositions_value: dict[str, Any] | None = None,
        ) -> None:
            projection_verification_path.write_bytes(
                pretty_json_bytes(verification_value)
            )
            projection_propositions_path.write_bytes(
                pretty_json_bytes(
                    base_projection_propositions
                    if propositions_value is None
                    else propositions_value
                )
            )

            def validate_projection_ledger() -> None:
                try:
                    validate_projection(
                        projection_authority_root,
                        expected_status=SOURCE_REVIEW_CANDIDATE_STATUS,
                    )
                except (AssertionError, ValueError, KeyError, TypeError) as error:
                    raise IntegrationError(
                        "reviewed authority projection ledger validation failed"
                    ) from error

            expect_integration_failure(
                validate_projection_ledger,
                f"semantic closure accepted projection-ledger drift: {label}",
            )

        missing_kind = copy.deepcopy(base_projection_verification)
        missing_kind["agent_visible_projection"]["excluded_kinds"].remove(
            "TCB_BOUNDARY"
        )
        reject_projection_ledger_mutation("missing-kind", missing_kind)
        stale_kind = copy.deepcopy(base_projection_verification)
        stale_kind["agent_visible_projection"]["excluded_kinds"].append("STALE_KIND")
        reject_projection_ledger_mutation("stale-kind", stale_kind)
        duplicate_kind = copy.deepcopy(base_projection_verification)
        duplicate_kind["agent_visible_projection"]["excluded_kinds"].append("TCB")
        reject_projection_ledger_mutation("duplicate-kind", duplicate_kind)
        novel_kind_propositions = copy.deepcopy(base_projection_propositions)
        next(
            entry
            for entry in novel_kind_propositions["entries"]
            if entry["kind"] == "TCB_BOUNDARY"
        )["kind"] = "NOVEL_NON_RUST_KIND"
        reject_projection_ledger_mutation(
            "novel-proposition-kind",
            copy.deepcopy(base_projection_verification),
            novel_kind_propositions,
        )

        authority_divergence = temp / "source-authority-divergence"
        copy_tree(source_review_candidate, authority_divergence)
        make_tree_writable(authority_divergence)
        authority_path = authority_divergence / "docs/rust-documentation.json"
        authority_path.write_bytes(authority_path.read_bytes() + b" ")
        expect_integration_failure(
            lambda: validate_source_review_payload(authority_divergence),
            "source review accepted authority bytes divergent from canonical projection",
        )

        fixture_binding_forgery = temp / "source-fixture-binding-forgery"
        copy_tree(source_review_candidate, fixture_binding_forgery)
        make_tree_writable(fixture_binding_forgery)
        fixture_path = fixture_binding_forgery / "reviewed-static/freeze/fixtures/E.json"
        fixture = read_json(fixture_path)
        fixture["source_tree_sha256"] = "0" * 64
        fixture_path.write_bytes(pretty_json_bytes(fixture))
        expect_integration_failure(
            lambda: validate_source_review_payload(fixture_binding_forgery),
            "source review accepted a caller-selected fixture source digest",
        )

        stale_marker_forgery = temp / "source-draft-marker-forgery"
        copy_tree(source_review_candidate, stale_marker_forgery)
        make_tree_writable(stale_marker_forgery)
        oracle_path = stale_marker_forgery / "reviewed-static/freeze/oracle/E.md"
        oracle_path.write_bytes(
            oracle_path.read_bytes().replace(
                b"**SOURCE-REVIEW-CANDIDATE / evaluator-only.**",
                b"**DRAFT / evaluator-only.**",
                1,
            )
        )
        expect_integration_failure(
            lambda: reject_reviewed_static_residue(
                stale_marker_forgery / "reviewed-static"
            ),
            "reviewed source accepted a stale DRAFT oracle marker",
        )
        for reviewer_index in range(1, 4):
            source_private_copy = temp / f"source-review-private-{reviewer_index}"
            prepare_source_review_copy(source_review_candidate, source_private_copy)
            verify_source_review_custody(source_review_candidate, source_private_copy)
        expect_integration_failure(
            lambda: verify_source_review_custody(
                source_review_candidate, source_review_candidate
            ),
            "source-review custody accepted a reflexive private copy",
        )
        observed_quotation_handoff: dict[str, Any] = {}

        def fake_online_quotation_validator(
            freeze_root: Path,
            *,
            expected_status: str,
            supplied_source_root: Path,
        ) -> str:
            observed_quotation_handoff.update(
                {
                    "freeze_root": freeze_root,
                    "expected_status": expected_status,
                    "supplied_source_root": supplied_source_root,
                }
            )
            return EXACT_QUOTATION_EVIDENCE_SHA256

        verify_source_review_quotations(
            source_private_copy,
            online_validator=fake_online_quotation_validator,
        )
        if observed_quotation_handoff != {
            "freeze_root": source_private_copy.resolve()
            / "reviewed-static"
            / "freeze",
            "expected_status": SOURCE_REVIEW_CANDIDATE_STATUS,
            "supplied_source_root": source_private_copy.resolve()
            / SOURCE_REVIEW_THEOREM_ROOT
            / "unsafe-rust",
        }:
            raise AssertionError(
                "source quotation CLI seam passed the wrong authenticated phase/root"
            )
        source_review_receipts = temp / "source-review-receipts"
        write_synthetic_source_review_receipts(
            source_review_candidate, source_review_receipts
        )
        source_receipt_template = read_json(
            source_review_receipts / "oracle-review-1.json"
        )
        incomplete_source_work_path = temp / "incomplete-source-work-product.json"
        incomplete_source_work = source_receipt_template["work_product"]
        incomplete_source_work["coverage"][0]["decision"] = "UNRESOLVED"
        incomplete_source_work_path.write_bytes(
            pretty_json_bytes(incomplete_source_work)
        )
        source_result_path = temp / "source-result.json"
        source_result_path.write_bytes(
            pretty_json_bytes(source_receipt_template["result"])
        )
        expect_integration_failure(
            lambda: build_source_review_receipt(
                snapshot=source_review_candidate,
                private_copy=source_review_candidate,
                review_name="oracle-review-1.json",
                actor_id="independent-source-reviewer-0001",
                work_product_path=incomplete_source_work_path,
                result_path=source_result_path,
                output=temp / "reflexive-source-review" / "oracle-review-1.json",
            ),
            "source receipt builder accepted the review subject as its private copy",
        )
        expect_integration_failure(
            lambda: build_source_review_receipt(
                snapshot=source_review_candidate,
                private_copy=source_private_copy,
                review_name="oracle-review-1.json",
                actor_id="independent-source-reviewer-0001",
                work_product_path=incomplete_source_work_path,
                result_path=source_result_path,
                output=temp / "wrong-source-receipt-name.json",
            ),
            "source receipt builder accepted a filename different from review_name",
        )
        rejected_source_output = temp / "oracle-review-1.json"
        expect_integration_failure(
            lambda: build_source_review_receipt(
                snapshot=source_review_candidate,
                private_copy=source_private_copy,
                review_name="oracle-review-1.json",
                actor_id="independent-source-reviewer-0001",
                work_product_path=incomplete_source_work_path,
                result_path=source_result_path,
                output=rejected_source_output,
            ),
            "source receipt builder invented a PASS for unresolved reviewer work",
        )
        if rejected_source_output.exists():
            raise AssertionError("failed source receipt build published an output")
        valid_source_work_path = temp / "valid-source-work-product.json"
        valid_source_work_path.write_bytes(
            pretty_json_bytes(
                read_json(source_review_receipts / "oracle-review-1.json")[
                    "work_product"
                ]
            )
        )
        incomplete_source_result_path = temp / "incomplete-source-result.json"
        incomplete_source_result = read_json(
            source_review_receipts / "oracle-review-1.json"
        )["result"]
        incomplete_source_result["checks"][0]["evidence"] = ""
        incomplete_source_result_path.write_bytes(
            pretty_json_bytes(incomplete_source_result)
        )
        expect_integration_failure(
            lambda: build_source_review_receipt(
                snapshot=source_review_candidate,
                private_copy=source_private_copy,
                review_name="oracle-review-1.json",
                actor_id="independent-source-reviewer-0001",
                work_product_path=valid_source_work_path,
                result_path=incomplete_source_result_path,
                output=rejected_source_output,
            ),
            "source receipt builder invented missing reviewer evidence",
        )
        if rejected_source_output.exists():
            raise AssertionError("failed source evidence build published an output")
        missing_source_receipt = temp / "missing-source-review-receipt"
        copy_tree(source_review_receipts, missing_source_receipt)
        (missing_source_receipt / "oracle-review-2.json").unlink()
        expect_integration_failure(
            lambda: validate_source_review_receipts(
                missing_source_receipt,
                snapshot_root=source_review_candidate,
                descriptor_sha256=sha256(
                    (source_review_candidate / SOURCE_REVIEW_DESCRIPTOR).read_bytes()
                ),
                manifest_sha256=sha256(
                    (source_review_candidate / SOURCE_REVIEW_MANIFEST).read_bytes()
                ),
                payload_sha256=read_json(
                    source_review_candidate / SOURCE_REVIEW_DESCRIPTOR
                )["payload_manifest_sha256"],
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "source review accepted a missing independent receipt",
        )
        wrong_source_check = temp / "wrong-source-review-check"
        copy_tree(source_review_receipts, wrong_source_check)
        wrong_receipt_path = wrong_source_check / "oracle-review-1.json"
        wrong_receipt = read_json(wrong_receipt_path)
        wrong_receipt["result"]["checks"][3]["id"] = "ARBITRARY-PASS"
        wrong_receipt_path.write_bytes(pretty_json_bytes(wrong_receipt))
        expect_integration_failure(
            lambda: validate_source_review_receipts(
                wrong_source_check,
                snapshot_root=source_review_candidate,
                descriptor_sha256=sha256(
                    (source_review_candidate / SOURCE_REVIEW_DESCRIPTOR).read_bytes()
                ),
                manifest_sha256=sha256(
                    (source_review_candidate / SOURCE_REVIEW_MANIFEST).read_bytes()
                ),
                payload_sha256=read_json(
                    source_review_candidate / SOURCE_REVIEW_DESCRIPTOR
                )["payload_manifest_sha256"],
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "source review accepted a generic PASS in place of exact check coverage",
        )
        special_source_receipts = temp / "special-source-review-entry"
        copy_tree(source_review_receipts, special_source_receipts)
        os.mkfifo(special_source_receipts / "extra.fifo")
        expect_integration_failure(
            lambda: validate_source_review_receipts(
                special_source_receipts,
                snapshot_root=source_review_candidate,
                descriptor_sha256=sha256(
                    (source_review_candidate / SOURCE_REVIEW_DESCRIPTOR).read_bytes()
                ),
                manifest_sha256=sha256(
                    (source_review_candidate / SOURCE_REVIEW_MANIFEST).read_bytes()
                ),
                payload_sha256=read_json(
                    source_review_candidate / SOURCE_REVIEW_DESCRIPTOR
                )["payload_manifest_sha256"],
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "source-review receipt inventory ignored a special entry",
        )
        production_inputs = temp / "production-inputs"
        expect_integration_failure(
            lambda: finalize_reviewed_inputs(
                snapshot=source_review_candidate,
                receipts=source_review_receipts,
                output=temp / "forbidden-synthetic-source-review-finalization",
            ),
            "synthetic source-review receipts authorized public production inputs",
        )
        _finalize_reviewed_inputs(
            snapshot=source_review_candidate,
            receipts=source_review_receipts,
            output=production_inputs,
            synthetic_capability=_SYNTHETIC_CAPABILITY,
        )
        for receipt_name, _review_kind in SOURCE_REVIEW_KINDS:
            if (
                production_inputs / "source-review-receipts" / receipt_name
            ).read_bytes() != (source_review_receipts / receipt_name).read_bytes():
                raise AssertionError(
                    "source-review finalization did not preserve exact receipt bytes"
                )
        production_snapshot = temp / "production-review-snapshot"
        production_workspace = Path("/tmp") / sha256(
            f"production-{temp}".encode()
        )
        _prepare_snapshot(
            source_root=trusted_unsafe_rust_root(),
            inputs=production_inputs,
            output=production_snapshot,
            workspace_base=production_workspace,
            declaration_path=SOURCE_DECLARATION,
            bundle_kind="SYNTHETIC-TEST-ONLY",
            synthetic_capability=_SYNTHETIC_CAPABILITY,
        )
        same_hook = sorted(EXTERNAL_REVIEW_HOOKS)[0]
        expect_integration_failure(
            lambda: build_snapshot_review_receipt(
                snapshot=production_snapshot,
                private_copy=production_snapshot,
                hook_id=same_hook,
                actor_id="independent-snapshot-reviewer-0001",
                work_product_path=temp / "unused-snapshot-work.json",
                result_path=temp / "unused-snapshot-result.json",
                output=temp / "wrong-snapshot-receipt-name.json",
            ),
            "snapshot receipt builder accepted a filename different from its hook ID",
        )
        expect_integration_failure(
            lambda: build_snapshot_review_receipt(
                snapshot=production_snapshot,
                private_copy=production_snapshot,
                hook_id=same_hook,
                actor_id="independent-snapshot-reviewer-0001",
                work_product_path=temp / "unused-snapshot-work.json",
                result_path=temp / "unused-snapshot-result.json",
                output=temp / "reflexive-snapshot-review" / f"{same_hook}.json",
            ),
            "snapshot receipt builder accepted the review subject as its private copy",
        )
        stale_schema_forgery = temp / "agent-visible-stale-schema-forgery"
        copy_tree(production_snapshot, stale_schema_forgery)
        make_tree_writable(stale_schema_forgery)
        evaluator_contract = read_json(
            stale_schema_forgery
            / "static/generated/evaluator-launch-contracts.json"
        )
        evaluator_schema_path = evaluator_contract["assignments"][0][
            "schema_paths"
        ][0]
        evaluator_schema = read_json(stale_schema_forgery / evaluator_schema_path)
        evaluator_schema["$comment"] = (
            "DRAFT / UNSEALED substituted evaluator-visible schema"
        )
        (stale_schema_forgery / evaluator_schema_path).write_bytes(
            pretty_json_bytes(evaluator_schema)
        )
        expect_integration_failure(
            lambda: validate_snapshot_build_products(
                stale_schema_forgery, bundle_kind="SYNTHETIC-TEST-ONLY"
            ),
            "snapshot accepted stale DRAFT lifecycle prose in an evaluator schema",
        )
        for field in ("source_tree_sha256", "exact_report_material_set_sha256"):
            ready_fixture_forgery = temp / f"ready-fixture-forgery-{field}"
            copy_tree(production_snapshot, ready_fixture_forgery)
            make_tree_writable(ready_fixture_forgery)
            ready_fixture_path = ready_fixture_forgery / "freeze/fixtures/E.json"
            ready_fixture = read_json(ready_fixture_path)
            ready_fixture[field] = "0" * 64
            ready_fixture_path.write_bytes(pretty_json_bytes(ready_fixture))
            expect_integration_failure(
                lambda ready_fixture_forgery=ready_fixture_forgery: validate_snapshot_build_products(
                    ready_fixture_forgery, bundle_kind="SYNTHETIC-TEST-ONLY"
                ),
                f"snapshot validation accepted forged fixture binding {field}",
            )

        report_binding_forgery = temp / "coherent-report-material-forgery"
        copy_tree(production_snapshot, report_binding_forgery)
        make_tree_writable(report_binding_forgery)
        forged_generated = report_binding_forgery / "static/generated"
        forged_prompt_path = forged_generated / "report-prompts/r001.md"
        forged_prompt_path.write_bytes(forged_prompt_path.read_bytes() + b"\ncoherent mutation\n")
        forged_launch_path = forged_generated / "launch-records/r001.json"
        forged_launch = read_json(forged_launch_path)
        forged_launch["prompt_sha256"] = sha256(forged_prompt_path.read_bytes())
        forged_launch_path.write_bytes(pretty_json_bytes(forged_launch))
        forged_prompt_receipt_path = forged_generated / "prompt-validation-receipt.json"
        forged_prompt_receipt = read_json(forged_prompt_receipt_path)
        forged_prompt_receipt["launch_record_sha256"]["r001"] = sha256(
            forged_launch_path.read_bytes()
        )
        forged_prompt_receipt_path.write_bytes(pretty_json_bytes(forged_prompt_receipt))
        forged_prompt_set_path = forged_generated / "mode-launch-prompt-set.json"
        forged_prompt_set = read_json(forged_prompt_set_path)
        forged_record = next(
            record
            for mode_record in forged_prompt_set["modes"]
            for record in mode_record["records"]
            if record["run_id"] == "r001"
        )
        forged_record["prompt_sha256"] = sha256(forged_prompt_path.read_bytes())
        forged_prompt_set_path.write_bytes(pretty_json_bytes(forged_prompt_set))
        forged_documents = {
            name: read_json(forged_generated / name)
            for name in prepare.generated_documents(
                prepare.validate_packages(read_json(report_binding_forgery / "packages.json")),
                prepare.validate_targets(read_json(report_binding_forgery / "targets.json")),
                prepare.validate_seeds(read_json(forged_generated / "seeds.json")),
                status="READY",
            )
        }
        forged_material = {
            "prompts": {
                path.stem: path.read_bytes()
                for path in (forged_generated / "report-prompts").glob("*.md")
            },
            "input_plans": {
                path.stem: path.read_bytes()
                for path in (forged_generated / "report-input-plans").glob("*.json")
            },
            "launches": {
                path.stem: path.read_bytes()
                for path in (forged_generated / "launch-records").glob("*.json")
            },
        }
        forged_material_digests = mode_report_material_digests(
            forged_material, forged_documents
        )
        forged_target_label = next(
            row["target_label"]
            for row in forged_documents["launch-schedule.json"]["slots"]
            if row["run_id"] == "r001"
        )
        forged_mode = next(
            row["mode"]
            for row in forged_documents["target-map.json"]["targets"]
            if row["target_label"] == forged_target_label
        )
        forged_fixture_path = report_binding_forgery / f"freeze/fixtures/{forged_mode}.json"
        forged_fixture = read_json(forged_fixture_path)
        forged_fixture["exact_report_material_set_sha256"] = forged_material_digests[
            forged_mode
        ]
        forged_fixture_path.write_bytes(pretty_json_bytes(forged_fixture))
        expect_integration_failure(
            lambda: validate_snapshot_build_products(
                report_binding_forgery, bundle_kind="SYNTHETIC-TEST-ONLY"
            ),
            "snapshot accepted a coherent prompt/launch/fixture report-material forgery",
        )
        verify_review_snapshot(
            production_snapshot,
            expected_candidate_kind="SYNTHETIC-TEST-ONLY",
        )
        production_receipts = temp / "production-receipts"
        write_synthetic_snapshot_receipts(
            production_snapshot,
            production_receipts,
            candidate_kind="SYNTHETIC-TEST-ONLY",
        )
        production_descriptor = read_json(
            production_snapshot / SNAPSHOT_DESCRIPTOR
        )
        receipt_names = sorted(
            f"{hook_id}.json" for hook_id in EXTERNAL_REVIEW_HOOKS
        )
        # Exercise the entire public PRODUCTION mechanical path with canonical
        # 0444 receipts authored through the public builders. The fixture work
        # products are test data, not an assertion that independent humans
        # performed these reviews; reviewer honesty remains an admitted TCB
        # premise. This regression exists to prove that genuine production-
        # shaped custody and finalization mechanics are executable.
        mechanical_source_receipts = temp / "mechanical-production-source-receipts"
        for reviewer_index, (receipt_name, _review_kind) in enumerate(
            SOURCE_REVIEW_KINDS, start=1
        ):
            private_copy = temp / f"mechanical-source-private-{reviewer_index}"
            prepare_source_review_copy(source_review_candidate, private_copy)
            template = read_json(source_review_receipts / receipt_name)
            work_path = temp / f"mechanical-source-work-{reviewer_index}.json"
            result_path = temp / f"mechanical-source-result-{reviewer_index}.json"
            work_path.write_bytes(pretty_json_bytes(template["work_product"]))
            result_path.write_bytes(pretty_json_bytes(template["result"]))
            build_source_review_receipt(
                snapshot=source_review_candidate,
                private_copy=private_copy,
                review_name=receipt_name,
                actor_id=f"mechanical-source-reviewer-{reviewer_index:04d}",
                work_product_path=work_path,
                result_path=result_path,
                output=mechanical_source_receipts / receipt_name,
            )
        mechanical_reviewed_inputs = temp / "mechanical-production-reviewed-inputs"
        finalize_reviewed_inputs(
            snapshot=source_review_candidate,
            receipts=mechanical_source_receipts,
            output=mechanical_reviewed_inputs,
        )
        mechanical_snapshot = temp / "mechanical-production-review-snapshot"
        prepare_snapshot(
            source_root=trusted_unsafe_rust_root(),
            inputs=mechanical_reviewed_inputs,
            output=mechanical_snapshot,
            workspace_base=Path("/tmp")
            / sha256(f"mechanical-production-{temp}".encode()),
        )
        mechanical_snapshot_templates = temp / "mechanical-snapshot-templates"
        write_synthetic_snapshot_receipts(
            mechanical_snapshot,
            mechanical_snapshot_templates,
            candidate_kind="PRODUCTION",
        )
        mechanical_snapshot_receipts = temp / "mechanical-production-snapshot-receipts"
        for reviewer_index, hook_id in enumerate(
            sorted(EXTERNAL_REVIEW_HOOKS), start=1
        ):
            private_copy = temp / f"mechanical-snapshot-private-{reviewer_index}"
            prepare_private_review_copy(mechanical_snapshot, private_copy)
            template = read_json(
                mechanical_snapshot_templates / f"{hook_id}.json"
            )
            work_path = temp / f"mechanical-snapshot-work-{reviewer_index}.json"
            result_path = temp / f"mechanical-snapshot-result-{reviewer_index}.json"
            work_path.write_bytes(pretty_json_bytes(template["work_product"]))
            result_path.write_bytes(pretty_json_bytes(template["result"]))
            build_snapshot_review_receipt(
                snapshot=mechanical_snapshot,
                private_copy=private_copy,
                hook_id=hook_id,
                actor_id=f"mechanical-snapshot-reviewer-{reviewer_index:04d}",
                work_product_path=work_path,
                result_path=result_path,
                output=mechanical_snapshot_receipts / f"{hook_id}.json",
            )
        mechanical_bundle = temp / "mechanical-production-bundle"
        mechanical_commitment_path = temp / "mechanical-production-commitment.json"
        mechanical_commitment = finalize_snapshot(
            snapshot=mechanical_snapshot,
            receipts=mechanical_snapshot_receipts,
            output=mechanical_bundle,
            external_commitment_output=mechanical_commitment_path,
        )
        (
            mechanical_lock,
            mechanical_reviewer_ids,
            mechanical_review_evidence,
        ) = verify_static_with_review_evidence(
            mechanical_bundle,
            expected_bundle_kind="PRODUCTION",
            expected_external_commitment=mechanical_commitment,
        )
        mechanical_source_evidence = mechanical_review_evidence[
            "source_review_receipts"
        ]
        mechanical_snapshot_evidence = mechanical_review_evidence[
            "snapshot_review_receipts"
        ]
        expected_mechanical_actors = {
            record["receipt"]["actor"]["identity"]
            for record in [*mechanical_source_evidence, *mechanical_snapshot_evidence]
        }
        if (
            mechanical_lock["bundle_kind"] != "PRODUCTION"
            or len(mechanical_reviewer_ids) != 11
            or mechanical_reviewer_ids != expected_mechanical_actors
            or mechanical_review_evidence["static_lock_sha256"]
            != sha256((mechanical_bundle / STATIC_LOCK).read_bytes())
            or [record["name"] for record in mechanical_source_evidence]
            != [name for name, _kind in SOURCE_REVIEW_KINDS]
            or [record["hook_id"] for record in mechanical_snapshot_evidence]
            != sorted(EXTERNAL_REVIEW_HOOKS)
            or any(
                record["receipt_sha256"]
                != sha256(
                    (
                        mechanical_bundle
                        / "static/integration/reviewed-inputs/source-review-receipts"
                        / record["name"]
                    ).read_bytes()
                )
                for record in mechanical_source_evidence
            )
            or any(
                record["receipt_sha256"]
                != sha256(
                    (
                        mechanical_bundle
                        / "static/integration-receipts"
                        / f"{record['hook_id']}.json"
                    ).read_bytes()
                )
                for record in mechanical_snapshot_evidence
            )
            or mechanical_commitment_path.read_bytes()
            != canonical_json_bytes(mechanical_commitment)
        ):
            raise AssertionError(
                "public mechanical PRODUCTION finalization did not verify exactly"
            )
        # A valid receipt path may be atomically replaced after validation. The
        # finalizer must publish the bytes captured from the validated descriptor,
        # never reopen that path and accidentally copy a different valid receipt.
        substitution_receipts = temp / "snapshot-receipt-substitution"
        copy_tree(production_receipts, substitution_receipts)
        for reviewer_index, receipt_name in enumerate(receipt_names, start=1):
            production_receipt_path = substitution_receipts / receipt_name
            production_receipt = read_json(production_receipt_path)
            production_receipt["status"] = "PASS"
            production_receipt["actor"]["identity"] = (
                f"independent-snapshot-reviewer-{reviewer_index:04d}"
            )
            production_receipt_path.write_bytes(
                canonical_json_bytes(production_receipt)
            )
            os.chmod(production_receipt_path, 0o444)
        substitution_name = receipt_names[0]
        substitution_path = substitution_receipts / substitution_name
        receipt_a = substitution_path.read_bytes()
        receipt_b_value = read_json(substitution_path)
        receipt_b_value["actor"]["identity"] = "alternate-snapshot-reviewer-9999"
        receipt_b = canonical_json_bytes(receipt_b_value)
        receipt_b_path = temp / "valid-substitute-snapshot-receipt.json"
        receipt_b_path.write_bytes(receipt_b)
        os.chmod(receipt_b_path, 0o444)
        validate_snapshot_review_receipt(
            receipt_b_path,
            substitution_path.stem,
            production_snapshot,
            production_descriptor,
        )
        real_capture_review_receipt_json = capture_review_receipt_json
        substitution_fired = False

        def substitute_snapshot_receipt_after_capture(
            path: Path,
            label: str,
            *,
            synthetic_capability: object | None,
        ) -> tuple[Any, bytes]:
            nonlocal substitution_fired
            value, data = real_capture_review_receipt_json(
                path, label, synthetic_capability=synthetic_capability
            )
            if path == substitution_path and not substitution_fired:
                os.replace(receipt_b_path, substitution_path)
                substitution_fired = True
            return value, data

        globals()["capture_review_receipt_json"] = (
            substitute_snapshot_receipt_after_capture
        )
        substitution_stage = temp / "snapshot-receipt-substitution-stage"
        try:
            copy_snapshot_review_receipts(
                substitution_stage,
                production_snapshot,
                substitution_receipts,
                production_descriptor,
                synthetic_capability=None,
            )
        finally:
            globals()["capture_review_receipt_json"] = (
                real_capture_review_receipt_json
            )
        copied_substitution = (
            substitution_stage
            / "static"
            / "integration-receipts"
            / substitution_name
        ).read_bytes()
        if (
            not substitution_fired
            or substitution_path.read_bytes() != receipt_b
            or copied_substitution != receipt_a
        ):
            raise AssertionError(
                "snapshot receipt finalization did not preserve descriptor-captured bytes"
            )
        special_snapshot_receipts = temp / "special-snapshot-review-entry"
        copy_tree(production_receipts, special_snapshot_receipts)
        os.mkfifo(special_snapshot_receipts / "extra.fifo")
        expect_integration_failure(
            lambda: copy_snapshot_review_receipts(
                temp / "special-snapshot-review-stage",
                production_snapshot,
                special_snapshot_receipts,
                production_descriptor,
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "snapshot-review receipt inventory ignored a special entry",
        )
        duplicate_snapshot_receipts = temp / "duplicate-snapshot-reviewers"
        copy_tree(production_receipts, duplicate_snapshot_receipts)
        first_snapshot_receipt = read_json(
            duplicate_snapshot_receipts / receipt_names[0]
        )
        second_snapshot_receipt_path = (
            duplicate_snapshot_receipts / receipt_names[1]
        )
        second_snapshot_receipt = read_json(second_snapshot_receipt_path)
        second_snapshot_receipt["actor"]["identity"] = (
            first_snapshot_receipt["actor"]["identity"]
        )
        second_snapshot_receipt_path.write_bytes(
            pretty_json_bytes(second_snapshot_receipt)
        )
        expect_integration_failure(
            lambda: copy_snapshot_review_receipts(
                temp / "duplicate-snapshot-reviewer-stage",
                production_snapshot,
                duplicate_snapshot_receipts,
                production_descriptor,
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "snapshot finalization accepted duplicate reviewer identities",
        )
        overlapping_snapshot_receipts = temp / "overlapping-reviewers"
        copy_tree(production_receipts, overlapping_snapshot_receipts)
        overlap_path = overlapping_snapshot_receipts / receipt_names[0]
        overlap_receipt = read_json(overlap_path)
        source_actor = read_json(
            production_snapshot
            / "static/integration/reviewed-inputs/source-review-receipts"
            / SOURCE_REVIEW_KINDS[0][0]
        )["actor"]["identity"]
        overlap_receipt["actor"]["identity"] = source_actor
        overlap_path.write_bytes(pretty_json_bytes(overlap_receipt))
        expect_integration_failure(
            lambda: copy_snapshot_review_receipts(
                temp / "overlapping-reviewer-stage",
                production_snapshot,
                overlapping_snapshot_receipts,
                production_descriptor,
                synthetic_capability=_SYNTHETIC_CAPABILITY,
            ),
            "snapshot finalization reused a source reviewer identity",
        )
        renamed_synthetic_receipt_path = production_receipts / (
            f"{sorted(EXTERNAL_REVIEW_HOOKS)[0]}.json"
        )
        renamed_synthetic_receipt = read_json(renamed_synthetic_receipt_path)
        renamed_synthetic_receipt["actor"]["identity"] = (
            "apparently-independent-reviewer-01"
        )
        renamed_synthetic_path = temp / "renamed-synthetic-receipt.json"
        renamed_synthetic_path.write_bytes(
            pretty_json_bytes(renamed_synthetic_receipt)
        )
        expect_integration_failure(
            lambda: validate_snapshot_review_receipt(
                renamed_synthetic_path,
                renamed_synthetic_receipt["hook_id"],
                production_snapshot,
                read_json(production_snapshot / SNAPSHOT_DESCRIPTOR),
            ),
            "renaming a synthetic actor made its test-only receipt production-acceptable",
        )
        atomic_swap_output = temp / "atomic-swap-final-output"
        atomic_swap_bundle = temp / "atomic-swap-substitute-bundle"
        copy_tree(output, atomic_swap_bundle)
        real_bundle_publish = publish_no_replace

        def substitute_valid_bundle(
            stage_path: Path, destination_path: Path
        ) -> None:
            if destination_path == atomic_swap_output:
                real_bundle_publish(atomic_swap_bundle, destination_path)
            else:
                real_bundle_publish(stage_path, destination_path)

        globals()["publish_no_replace"] = substitute_valid_bundle
        try:
            expect_integration_failure(
                lambda: _finalize_snapshot(
                    snapshot=production_snapshot,
                    receipts=production_receipts,
                    output=atomic_swap_output,
                    bundle_kind="SYNTHETIC-TEST-ONLY",
                    synthetic_capability=_SYNTHETIC_CAPABILITY,
                ),
                "finalization blessed a coherently substituted bundle after publication",
            )
        finally:
            globals()["publish_no_replace"] = real_bundle_publish
        verify_static(
            atomic_swap_output,
            expected_bundle_kind="SYNTHETIC-TEST-ONLY",
            expected_external_commitment=commitment,
        )
        production_output = temp / "production-bundle"
        production_commitment_path = temp / "production-external-commitment.json"
        expect_integration_failure(
            lambda: finalize_snapshot(
                snapshot=production_snapshot,
                receipts=production_receipts,
                output=temp / "forbidden-public-production-bundle",
                external_commitment_output=temp / "forbidden-public-commitment.json",
            ),
            "synthetic snapshot/receipts authorized public PRODUCTION finalization",
        )
        production_commitment = _finalize_snapshot(
            snapshot=production_snapshot,
            receipts=production_receipts,
            output=production_output,
            bundle_kind="SYNTHETIC-TEST-ONLY",
            synthetic_capability=_SYNTHETIC_CAPABILITY,
            external_commitment_output=production_commitment_path,
        )
        if read_json(production_commitment_path) != production_commitment:
            raise AssertionError("finalizer did not write its exact external commitment")
        verify_static(
            production_output,
            expected_bundle_kind="SYNTHETIC-TEST-ONLY",
            expected_external_commitment=production_commitment,
        )
        # Static verification must bind the lock digest, semantic validation,
        # and runtime reviewer-exclusion identity to one captured receipt byte
        # object. Swap the path to a separately valid receipt after capture; the
        # substitute deliberately collides with a source reviewer, so a later
        # pathname reread would fail rather than silently consume A.
        verify_swap_hook = sorted(EXTERNAL_REVIEW_HOOKS)[0]
        verify_receipt_root = production_output / "static/integration-receipts"
        verify_swap_path = verify_receipt_root / f"{verify_swap_hook}.json"
        verify_receipt_a = verify_swap_path.read_bytes()
        verify_receipt_b_value = read_json(verify_swap_path)
        verify_receipt_b_value["actor"]["identity"] = read_json(
            production_output
            / "static/integration/reviewed-inputs/source-review-receipts"
            / SOURCE_REVIEW_KINDS[0][0]
        )["actor"]["identity"]
        verify_receipt_b = pretty_json_bytes(verify_receipt_b_value)
        verify_receipt_b_path = temp / "static-verifier-receipt-B.json"
        verify_receipt_b_path.write_bytes(verify_receipt_b)
        os.chmod(verify_receipt_b_path, 0o444)
        validate_snapshot_review_receipt(
            verify_receipt_b_path,
            verify_swap_hook,
            production_output,
            read_json(production_output / SNAPSHOT_DESCRIPTOR),
            synthetic_capability=_SYNTHETIC_CAPABILITY,
        )
        real_captured_receipt_validator = (
            _validate_snapshot_review_receipt_captured
        )
        static_verify_substitution_fired = False

        def substitute_static_receipt_after_capture(
            path: Path,
            expected_hook: str,
            snapshot: Path,
            descriptor: dict[str, Any],
            *,
            synthetic_capability: object | None = None,
        ) -> tuple[dict[str, Any], bytes]:
            nonlocal static_verify_substitution_fired
            receipt, data = real_captured_receipt_validator(
                path,
                expected_hook,
                snapshot,
                descriptor,
                synthetic_capability=synthetic_capability,
            )
            if path == verify_swap_path and not static_verify_substitution_fired:
                os.chmod(verify_receipt_root, 0o755)
                try:
                    os.replace(verify_receipt_b_path, verify_swap_path)
                finally:
                    os.chmod(verify_receipt_root, 0o555)
                static_verify_substitution_fired = True
            return receipt, data

        globals()["_validate_snapshot_review_receipt_captured"] = (
            substitute_static_receipt_after_capture
        )
        substituted_review_evidence: dict[str, Any] | None = None
        try:
            _lock, _reviewer_ids, substituted_review_evidence = _verify_static_contents(
                production_output,
                expected_bundle_kind="SYNTHETIC-TEST-ONLY",
            )
        finally:
            globals()["_validate_snapshot_review_receipt_captured"] = (
                real_captured_receipt_validator
            )
            os.chmod(verify_receipt_root, 0o755)
            try:
                restore_receipt = temp / "static-verifier-receipt-A.json"
                restore_receipt.write_bytes(verify_receipt_a)
                os.chmod(restore_receipt, 0o444)
                os.replace(restore_receipt, verify_swap_path)
            finally:
                os.chmod(verify_receipt_root, 0o555)
        if (
            not static_verify_substitution_fired
            or substituted_review_evidence is None
            or next(
                record
                for record in substituted_review_evidence[
                    "snapshot_review_receipts"
                ]
                if record["hook_id"] == verify_swap_hook
            )["receipt_sha256"]
            != sha256(verify_receipt_a)
            or verify_swap_path.read_bytes() != verify_receipt_a
        ):
            raise AssertionError(
                "static receipt verifier did not consume one captured receipt object"
            )
        # Source receipts must be captured and joined to the already
        # authenticated static-manifest records. Replacing A with a separately
        # valid B after all snapshot receipts were captured must not let a later
        # reviewer-ID pathname reopen change the exclusion set.
        source_receipt_root = (
            production_output
            / "static/integration/reviewed-inputs/source-review-receipts"
        )
        source_swap_name = SOURCE_REVIEW_KINDS[0][0]
        source_swap_path = source_receipt_root / source_swap_name
        source_receipt_a = source_swap_path.read_bytes()
        source_receipt_b_value = read_json(source_swap_path)
        source_receipt_b_value["actor"]["identity"] = (
            "alternate-source-reviewer-9999"
        )
        source_receipt_b = pretty_json_bytes(source_receipt_b_value)
        source_receipt_b_path = temp / "static-verifier-source-receipt-B.json"
        source_receipt_b_path.write_bytes(source_receipt_b)
        os.chmod(source_receipt_b_path, 0o444)
        source_validation_root = temp / "source-receipt-B-validation"
        copy_tree(source_receipt_root, source_validation_root)
        make_tree_writable(source_validation_root)
        (source_validation_root / source_swap_name).write_bytes(source_receipt_b)
        reviewed_inputs = (
            production_output / "static/integration/reviewed-inputs"
        )
        reviewed_descriptor_bytes = (
            reviewed_inputs / SOURCE_REVIEW_DESCRIPTOR
        ).read_bytes()
        reviewed_manifest_bytes = (
            reviewed_inputs / SOURCE_REVIEW_MANIFEST
        ).read_bytes()
        reviewed_descriptor = parse_json_bytes(
            reviewed_descriptor_bytes, "source late-swap descriptor"
        )
        _validate_source_review_receipts_captured(
            source_validation_root,
            snapshot_root=reviewed_inputs,
            descriptor_sha256=sha256(reviewed_descriptor_bytes),
            manifest_sha256=sha256(reviewed_manifest_bytes),
            payload_sha256=reviewed_descriptor["payload_manifest_sha256"],
            synthetic_capability=_SYNTHETIC_CAPABILITY,
        )
        source_late_swap_snapshot_count = 0
        source_late_swap_fired = False

        def swap_source_after_snapshot_captures(
            path: Path,
            expected_hook: str,
            snapshot: Path,
            descriptor: dict[str, Any],
            *,
            synthetic_capability: object | None = None,
        ) -> tuple[dict[str, Any], bytes]:
            nonlocal source_late_swap_snapshot_count, source_late_swap_fired
            receipt, data = real_captured_receipt_validator(
                path,
                expected_hook,
                snapshot,
                descriptor,
                synthetic_capability=synthetic_capability,
            )
            source_late_swap_snapshot_count += 1
            if (
                source_late_swap_snapshot_count == len(EXTERNAL_REVIEW_HOOKS)
                and not source_late_swap_fired
            ):
                os.chmod(source_receipt_root, 0o755)
                try:
                    os.replace(source_receipt_b_path, source_swap_path)
                finally:
                    os.chmod(source_receipt_root, 0o555)
                source_late_swap_fired = True
            return receipt, data

        globals()["_validate_snapshot_review_receipt_captured"] = (
            swap_source_after_snapshot_captures
        )
        try:
            expect_integration_failure(
                lambda: _verify_static_contents(
                    production_output,
                    expected_bundle_kind="SYNTHETIC-TEST-ONLY",
                ),
                "late source-receipt substitution changed a verified exclusion set",
            )
        finally:
            globals()["_validate_snapshot_review_receipt_captured"] = (
                real_captured_receipt_validator
            )
            os.chmod(source_receipt_root, 0o755)
            try:
                source_restore = temp / "static-verifier-source-receipt-A.json"
                source_restore.write_bytes(source_receipt_a)
                os.chmod(source_restore, 0o444)
                os.replace(source_restore, source_swap_path)
            finally:
                os.chmod(source_receipt_root, 0o555)
        if not source_late_swap_fired:
            raise AssertionError(
                "late source-receipt substitution regression did not reach its seam"
            )
        verify_static(
            production_output,
            expected_bundle_kind="SYNTHETIC-TEST-ONLY",
            expected_external_commitment=production_commitment,
        )
        if stat.S_IMODE(
            production_commitment_path.stat(follow_symlinks=False).st_mode
        ) != 0o444:
            raise AssertionError("published external commitment is not read-only")
        expect_integration_failure(
            lambda: verify_static(
                production_output,
                expected_bundle_kind="PRODUCTION",
            ),
            "public verifier promoted a synthetic reviewed lifecycle to PRODUCTION",
        )
        wrong_production_commitment = {
            **production_commitment,
            "static_lock_sha256": "0" * 64,
        }
        expect_integration_failure(
            lambda: verify_static(
                production_output,
                expected_bundle_kind="SYNTHETIC-TEST-ONLY",
                expected_external_commitment=wrong_production_commitment,
            ),
            "public verifier accepted the wrong PRODUCTION commitment",
        )
        expect_integration_failure(
            lambda: load_separately_custodied_external_commitment(
                production_output, production_output / STATIC_LOCK
            ),
            "commitment loader accepted a candidate-local file",
        )
        expect_integration_failure(
            lambda: _publish_external_commitment_file(
                production_commitment_path, production_commitment
            ),
            "commitment publisher replaced an existing commitment",
        )

        expect_integration_failure(
            lambda: recover_external_commitment(
                root=production_output,
                output=temp / "forbidden-synthetic-recovery.json",
                custody_acknowledgement=RECOVERY_CUSTODY_ACKNOWLEDGEMENT,
            ),
            "production commitment recovery accepted a synthetic bundle",
        )

        trusted_protocol = __import__("protocol")
        def expect_protocol_failure(operation: Callable[[], Any], message: str) -> None:
            try:
                operation()
            except trusted_protocol.ProtocolError:
                return
            raise AssertionError(message)

        expect_protocol_failure(
            lambda: trusted_protocol.load_verified_static_bundle(
                production_output, production_commitment_path
            ),
            "trusted protocol accepted a SYNTHETIC-TEST-ONLY bundle as PRODUCTION",
        )
        expect_protocol_failure(
            lambda: trusted_protocol.load_verified_static_bundle(
                production_output, production_output / STATIC_LOCK
            ),
            "trusted protocol accepted an in-candidate external commitment",
        )
        candidate_protocol = types.ModuleType("_v5_candidate_protocol_sentinel")
        candidate_protocol.__file__ = str(production_output / "protocol.py")
        exec(
            compile(
                (production_output / "protocol.py").read_bytes(),
                str(production_output / "protocol.py"),
                "exec",
                dont_inherit=True,
            ),
            candidate_protocol.__dict__,
        )
        try:
            candidate_protocol.load_verified_static_bundle(
                production_output, production_commitment_path
            )
        except candidate_protocol.ProtocolError:
            pass
        else:
            raise AssertionError("candidate protocol bytes established a production trust root")

        (output / RUNTIME_STATE / "synthetic.json").write_text("{}\n", encoding="utf-8")
        verify_static(output, expected_bundle_kind="SYNTHETIC-TEST-ONLY")
        (output / RUNTIME_ROOT / "forbidden").mkdir()
        expect_integration_failure(
            lambda: verify_static(output, expected_bundle_kind="SYNTHETIC-TEST-ONLY"),
            "verify-static accepted a runtime sibling outside state",
        )
        (output / RUNTIME_ROOT / "forbidden").rmdir()
        tampered = prompts[0]
        os.chmod(tampered, 0o644)
        tampered.write_bytes(tampered.read_bytes() + b"tamper")
        expect_integration_failure(
            lambda: verify_static(output, expected_bundle_kind="SYNTHETIC-TEST-ONLY"),
            "verify-static accepted changed static bytes",
        )
    print("V5 snapshot/review/finalize mechanical-production and synthetic self-test passed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("draft", help="validate the unsealed source and mechanism")
    commands.add_parser(
        "reviewer-runtime-attestation",
        help="emit canonical JSON identifying the active reviewer Python/SSL runtime",
    )
    prepare_source = commands.add_parser(
        "prepare-source-review",
        help="derive and publish the immutable reviewed-source candidate",
    )
    prepare_source.add_argument("--source-root", type=Path, required=True)
    prepare_source.add_argument("--inputs", type=Path, required=True)
    prepare_source.add_argument("--output", type=Path, required=True)
    prepare_source.add_argument(
        "--acknowledge-source-review-values",
        action="store_true",
        required=True,
        help="confirm that the requested policies, invocation text, and seeds are intentional",
    )
    review_source = commands.add_parser(
        "review-source-subject",
        help="verify a source-review candidate and publish a private review copy",
    )
    review_source.add_argument("snapshot", type=Path)
    review_source.add_argument("--private-copy", type=Path, required=True)
    source_custody = commands.add_parser(
        "source-review-custody-check",
        help="reverify source-review candidate and private copy at review completion",
    )
    source_custody.add_argument("--snapshot", type=Path, required=True)
    source_custody.add_argument("--private-copy", type=Path, required=True)
    verify_quotations = commands.add_parser(
        "verify-source-quotations",
        help=(
            "fetch pinned official pages and verify every exact excerpt in a "
            "verified private source-review copy"
        ),
    )
    verify_quotations.add_argument("--private-copy", type=Path, required=True)
    build_source_receipt = commands.add_parser(
        "build-source-review-receipt",
        help=(
            "bind reviewer-authored work product and findings into one exact "
            "source-review receipt"
        ),
    )
    build_source_receipt.add_argument("--snapshot", type=Path, required=True)
    build_source_receipt.add_argument("--private-copy", type=Path, required=True)
    build_source_receipt.add_argument(
        "--review-name",
        choices=[name for name, _kind in SOURCE_REVIEW_KINDS],
        required=True,
    )
    build_source_receipt.add_argument("--actor-id", required=True)
    build_source_receipt.add_argument("--work-product", type=Path, required=True)
    build_source_receipt.add_argument("--result", type=Path, required=True)
    build_source_receipt.add_argument("--output", type=Path, required=True)
    validate_source_receipts = commands.add_parser(
        "validate-source-review-receipts",
        help="validate the exact three-receipt production source-review set",
    )
    validate_source_receipts.add_argument("--snapshot", type=Path, required=True)
    validate_source_receipts.add_argument("--receipts", type=Path, required=True)
    finalize_source = commands.add_parser(
        "finalize-reviewed-inputs",
        help="bind three exact independent source-review receipts without replacement",
    )
    finalize_source.add_argument("--snapshot", type=Path, required=True)
    finalize_source.add_argument("--receipts", type=Path, required=True)
    finalize_source.add_argument("--output", type=Path, required=True)
    finalize_source.add_argument(
        "--acknowledge-authenticated-source-reviewers",
        action="store_true",
        required=True,
        help="confirm out-of-band authentication of three distinct receipt actors",
    )
    prepare_command = commands.add_parser(
        "prepare-snapshot", help="materialize a complete PRODUCTION review candidate"
    )
    prepare_command.add_argument("--source-root", type=Path, required=True)
    prepare_command.add_argument("--inputs", type=Path, required=True)
    prepare_command.add_argument("--output", type=Path, required=True)
    prepare_command.add_argument("--workspace-base", type=Path, required=True)
    prepare_command.add_argument(
        "--acknowledge-reviewed-inputs",
        action="store_true",
        required=True,
        help="confirm the supplied values, reviewed overlay, and seeds are intentional",
    )
    review = commands.add_parser(
        "review-subject",
        help="verify a PRODUCTION candidate and publish a private review copy",
    )
    review.add_argument("snapshot", type=Path)
    review.add_argument("--private-copy", type=Path, required=True)
    custody = commands.add_parser(
        "review-custody-check",
        help="reverify the source and private review copy at review completion",
    )
    custody.add_argument("--snapshot", type=Path, required=True)
    custody.add_argument("--private-copy", type=Path, required=True)
    build_snapshot_receipt = commands.add_parser(
        "build-snapshot-review-receipt",
        help=(
            "bind reviewer-authored work product and findings into one exact "
            "snapshot-review receipt"
        ),
    )
    build_snapshot_receipt.add_argument("--snapshot", type=Path, required=True)
    build_snapshot_receipt.add_argument("--private-copy", type=Path, required=True)
    build_snapshot_receipt.add_argument(
        "--hook-id", choices=sorted(EXTERNAL_REVIEW_HOOKS), required=True
    )
    build_snapshot_receipt.add_argument("--actor-id", required=True)
    build_snapshot_receipt.add_argument("--work-product", type=Path, required=True)
    build_snapshot_receipt.add_argument("--result", type=Path, required=True)
    build_snapshot_receipt.add_argument("--output", type=Path, required=True)
    validate_snapshot_receipts = commands.add_parser(
        "validate-snapshot-review-receipts",
        help="validate the exact eight-receipt production snapshot-review set",
    )
    validate_snapshot_receipts.add_argument("--snapshot", type=Path, required=True)
    validate_snapshot_receipts.add_argument("--receipts", type=Path, required=True)
    finalize = commands.add_parser(
        "finalize", help="bind independent receipts and lock a PRODUCTION snapshot"
    )
    finalize.add_argument("--snapshot", type=Path, required=True)
    finalize.add_argument("--receipts", type=Path, required=True)
    finalize.add_argument("--output", type=Path, required=True)
    finalize.add_argument(
        "--external-commitment-output",
        type=Path,
        required=True,
        help="fresh coordinator-held file outside the bundle",
    )
    finalize.add_argument(
        "--acknowledge-reviewed-snapshot",
        action="store_true",
        required=True,
        help="confirm that the receipts came from review of this exact snapshot",
    )
    verify = commands.add_parser(
        "verify-static", help="verify a locked bundle as PRODUCTION by default"
    )
    verify.add_argument("root", type=Path)
    verify.add_argument(
        "--expected-bundle-kind",
        choices=BUNDLE_KINDS,
        default="PRODUCTION",
    )
    verify.add_argument(
        "--expected-external-commitment",
        type=Path,
        help=(
            "separately custodied commitment; mandatory for PRODUCTION and required "
            "to detect whole-bundle replacement"
        ),
    )
    recover_commitment = commands.add_parser(
        "recover-external-commitment",
        help=(
            "recover a missing PRODUCTION commitment only after an interrupted "
            "finalization under uninterrupted trusted custody"
        ),
    )
    recover_commitment.add_argument("root", type=Path)
    recover_commitment.add_argument("--output", type=Path, required=True)
    recover_commitment.add_argument(
        "--acknowledge-uninterrupted-custody-since-finalization",
        action="store_true",
        required=True,
        help=(
            "attest that this exact bundle has remained under uninterrupted trusted "
            "coordinator custody since successful finalization and that no external "
            "commitment was previously published"
        ),
    )
    commands.add_parser(
        "self-test",
        help="exercise snapshot/review/finalize/verify synthetically",
    )
    args = parser.parse_args()
    if args.command == "draft":
        draft()
    elif args.command == "reviewer-runtime-attestation":
        print(
            canonical_json_bytes(current_reviewer_runtime_attestation()).decode("utf-8"),
            end="",
        )
    elif args.command == "prepare-source-review":
        prepare_source_review(
            source_root=args.source_root,
            inputs=args.inputs,
            output=args.output,
        )
        print(f"wrote immutable source-review candidate: {args.output}")
    elif args.command == "review-source-subject":
        print(
            pretty_json_bytes(
                prepare_source_review_copy(args.snapshot, args.private_copy)
            ).decode("utf-8"),
            end="",
        )
    elif args.command == "source-review-custody-check":
        print(
            pretty_json_bytes(
                verify_source_review_custody(args.snapshot, args.private_copy)
            ).decode("utf-8"),
            end="",
        )
    elif args.command == "verify-source-quotations":
        verify_source_review_quotations(args.private_copy)
    elif args.command == "build-source-review-receipt":
        build_source_review_receipt(
            snapshot=args.snapshot,
            private_copy=args.private_copy,
            review_name=args.review_name,
            actor_id=args.actor_id,
            work_product_path=args.work_product,
            result_path=args.result,
            output=args.output,
        )
        print(f"wrote validated source-review receipt: {args.output}")
    elif args.command == "validate-source-review-receipts":
        validate_production_source_review_receipts(
            snapshot=args.snapshot, receipts=args.receipts
        )
        print("validated exact three-receipt production source-review set")
    elif args.command == "finalize-reviewed-inputs":
        finalize_reviewed_inputs(
            snapshot=args.snapshot,
            receipts=args.receipts,
            output=args.output,
        )
        print(f"wrote finalized reviewed snapshot inputs: {args.output}")
    elif args.command == "prepare-snapshot":
        prepare_snapshot(
            source_root=args.source_root,
            inputs=args.inputs,
            output=args.output,
            workspace_base=args.workspace_base,
        )
        print(f"wrote immutable review candidate: {args.output}")
    elif args.command == "review-subject":
        print(
            pretty_json_bytes(
                prepare_private_review_copy(args.snapshot, args.private_copy)
            ).decode("utf-8"),
            end="",
        )
    elif args.command == "review-custody-check":
        print(
            pretty_json_bytes(
                verify_private_review_custody(args.snapshot, args.private_copy)
            ).decode("utf-8"),
            end="",
        )
    elif args.command == "build-snapshot-review-receipt":
        build_snapshot_review_receipt(
            snapshot=args.snapshot,
            private_copy=args.private_copy,
            hook_id=args.hook_id,
            actor_id=args.actor_id,
            work_product_path=args.work_product,
            result_path=args.result,
            output=args.output,
        )
        print(f"wrote validated snapshot-review receipt: {args.output}")
    elif args.command == "validate-snapshot-review-receipts":
        validate_production_snapshot_review_receipts(
            snapshot=args.snapshot, receipts=args.receipts
        )
        print("validated exact eight-receipt production snapshot-review set")
    elif args.command == "finalize":
        commitment = finalize_snapshot(
            snapshot=args.snapshot,
            receipts=args.receipts,
            output=args.output,
            external_commitment_output=args.external_commitment_output,
        )
        print(f"wrote immutable PRODUCTION static bundle: {args.output}")
        print(
            "wrote external whole-bundle commitment: "
            f"{args.external_commitment_output} ({commitment['static_lock_sha256']})"
        )
    elif args.command == "verify-static":
        expected_commitment = None
        if (
            args.expected_bundle_kind == "PRODUCTION"
            and args.expected_external_commitment is None
        ):
            raise IntegrationError(
                "PRODUCTION CLI verification requires --expected-external-commitment; "
                "use recover-external-commitment only for an interrupted-finalization "
                "recovery under uninterrupted trusted custody"
            )
        if args.expected_external_commitment is not None:
            expected_commitment = load_separately_custodied_external_commitment(
                args.root, args.expected_external_commitment
            )
        lock = verify_static(
            args.root,
            expected_bundle_kind=args.expected_bundle_kind,
            expected_external_commitment=expected_commitment,
        )
        print(
            f"verified {lock['manifest_entry_count']} static files under {lock['status']}"
        )
    elif args.command == "recover-external-commitment":
        commitment = recover_external_commitment(
            root=args.root,
            output=args.output,
            custody_acknowledgement=(
                RECOVERY_CUSTODY_ACKNOWLEDGEMENT
                if args.acknowledge_uninterrupted_custody_since_finalization
                else ""
            ),
        )
        print(
            "recovered external whole-bundle commitment after trusted-custody "
            f"acknowledgement: {args.output} ({commitment['static_lock_sha256']})"
        )
    else:
        self_test()


if __name__ == "__main__":
    main()
