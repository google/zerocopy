#!/usr/bin/env python3
"""Prepare, review, finalize, and verify a V5 prelaunch static bundle.

Production integration is deliberately two-step. ``prepare-snapshot`` first
materializes every derived byte which semantic reviewers must inspect and
publishes an immutable REVIEW-CANDIDATE. Review receipts then bind that exact
snapshot. ``finalize`` copies and re-verifies the snapshot, adds only the bound
receipts and mechanical finalization records, and creates ``STATIC-LOCK.json``
as the final static byte mutation. There is no one-shot production path.

``self-test`` uses a private SYNTHETIC-TEST-ONLY capability and temporary
directories. It cannot mint a bundle which authenticates as PRODUCTION.
"""

from __future__ import annotations

import argparse
import ctypes
import errno
import hashlib
import json
import os
import re
import shutil
import stat
import tempfile
import types
from pathlib import Path
from typing import Any, Callable, Iterable

import prepare


RUN = Path(__file__).resolve().parent
SOURCE_DECLARATION = RUN / "static-inputs" / "source-declaration.json"
STATIC_MANIFEST = "STATIC-MANIFEST.sha256"
STATIC_LOCK = "STATIC-LOCK.json"
SNAPSHOT_MANIFEST = "REVIEW-SNAPSHOT.manifest"
SNAPSHOT_DESCRIPTOR = "REVIEW-SNAPSHOT.json"
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
SNAPSHOT_REVIEW_CHECK_IDS = (
    "EXACT-SNAPSHOT-BOUND",
    "REVIEW-CONTRACT-BOUND",
    "ARTIFACT-INVENTORY-CHECKED",
    "HOOK-SEMANTICS-CHECKED",
    "END-OF-REVIEW-REVERIFIED",
)


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


def _publish_external_commitment_file(path: Path, value: dict[str, Any]) -> None:
    """Durably stage, then no-replace-publish, a read-only commitment file."""

    destination = canonical_new_file_destination(path, "external commitment output")
    data = canonical_json_bytes(value)
    descriptor, stage_text = tempfile.mkstemp(
        prefix=f".{destination.name}.v5-commitment-stage-",
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
                "published external commitment is not the exact read-only staged file"
            )
    except Exception:
        if descriptor >= 0:
            os.close(descriptor)
        if os.path.lexists(stage):
            stage.unlink()
            fsync_directory(stage.parent)
        raise


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
        "time_budget_seconds",
        "tools",
        "network_access",
        "documentation_access",
        "hosted_build",
    }
    for role, raw in value.items():
        config = exact_object(raw, keys, f"execution config {role}")
        text_fields = keys - {"token_budget", "time_budget_seconds", "tools"}
        if any(
            not isinstance(config[key], str) or not config[key].strip()
            for key in text_fields
        ):
            raise IntegrationError(
                f"execution config {role} text fields must be declared nonblank strings"
            )
        if (
            not isinstance(config["tools"], list)
            or not config["tools"]
            or any(not isinstance(tool, str) or not tool.strip() for tool in config["tools"])
            or len(set(config["tools"])) != len(config["tools"])
        ):
            raise IntegrationError(f"execution config {role} has invalid tools")
        for integer in ("token_budget", "time_budget_seconds"):
            if type(config[integer]) is not int or config[integer] < 1:
                raise IntegrationError(f"execution config {role}.{integer} must be positive")
    return value


def validate_reviewed_values(value: Any, declaration_bytes: bytes) -> dict[str, Any]:
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
            "reviewed_static",
        },
        "reviewed values",
    )
    if reviewed["schema_version"] != 1 or reviewed["status"] != "READY":
        raise IntegrationError("reviewed values must be schema-v1 READY")
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
            "evidence_policy",
            "fresh_attempt_root_policy",
            "frozen_input_policy",
            "snapshot_policy",
            "bundle_kind_policy",
            "static_manifest_algorithm",
            "path_domain",
            "metadata_policy",
            "synthetic_test_policy",
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
        "evidence_policy": "POST_LOCK_COMMITTED_RUNTIME_STATE_REQUIRED_AT_INTEGRATION",
        "fresh_attempt_root_policy": "EXCLUSIVE_CREATE_ON_LEASE",
        "frozen_input_policy": "NO_MUTATION_AFTER_LOCK",
        "snapshot_policy": "REVIEW_EXACT_STAGED_PAYLOAD_BEFORE_FINALIZATION",
        "bundle_kind_policy": "LOCK_AND_STATUS_MUST_MATCH_CALLER_EXPECTED_KIND",
        "static_manifest_algorithm": MANIFEST_ALGORITHM,
        "path_domain": PATH_DOMAIN,
        "metadata_policy": "STATIC_FILES_0444_STATIC_DIRS_0555_RUNTIME_STATE_0700",
        "synthetic_test_policy": "PRIVATE_PATH_CAN_ONLY_MINT_SYNTHETIC_TEST_ONLY",
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
        "freeze/controls.json",
        "freeze/rules/defect-rules.json",
        "freeze/reviews/oracle-review-1.json",
        "freeze/reviews/oracle-review-2.json",
        "freeze/reviews/coherence-review.json",
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


def validate_reviewed_static(root: Path, records: Any) -> None:
    if not isinstance(records, list):
        raise IntegrationError("reviewed_static must be a list")
    observed: set[str] = set()
    for raw in records:
        record = exact_object(raw, {"path", "sha256", "decision"}, "static review")
        path_text = relative(record["path"], "static review path")
        if path_text in observed:
            raise IntegrationError(f"duplicate static review path: {path_text}")
        observed.add(path_text)
        if record["decision"] != "PASS":
            raise IntegrationError(f"static review is not PASS: {path_text}")
        path = root / path_text
        if path.is_symlink() or not path.is_file():
            raise IntegrationError(f"reviewed static path is not a regular file: {path_text}")
        if sha256(path.read_bytes()) != digest(record["sha256"], f"review {path_text}"):
            raise IntegrationError(f"reviewed static digest mismatch: {path_text}")
        if path.suffix == ".json" and not path_text.startswith("freeze/reviews/"):
            value = read_json(path)
            if not isinstance(value, dict) or value.get("status") != "READY":
                raise IntegrationError(f"reviewed JSON is not READY: {path_text}")
    expected = required_review_paths()
    if observed != expected:
        missing = sorted(expected - observed)
        extra = sorted(observed - expected)
        raise IntegrationError(f"static review path set mismatch; missing={missing}, extra={extra}")
    reviews = [
        read_json(root / "freeze" / "reviews" / name)
        for name in ("oracle-review-1.json", "oracle-review-2.json", "coherence-review.json")
    ]
    for index, review in enumerate(reviews):
        exact_object(
            review,
            {"schema_version", "status", "review_kind", "reviewer_id", "decision", "input_digests"},
            f"independent review {index}",
        )
        if (
            review["schema_version"] != 1
            or review["status"] != "READY"
            or review["decision"] != "PASS"
            or not isinstance(review["reviewer_id"], str)
            or not review["reviewer_id"]
            or not isinstance(review["input_digests"], dict)
            or not review["input_digests"]
            or any(not HEX64.fullmatch(item) for item in review["input_digests"].values())
        ):
            raise IntegrationError(f"invalid independent review {index}")
    if [review["review_kind"] for review in reviews] != [
        "INDEPENDENT_ORACLE",
        "INDEPENDENT_ORACLE",
        "COHERENCE",
    ]:
        raise IntegrationError("review kinds are not two oracle reviews plus coherence")
    if len({review["reviewer_id"] for review in reviews}) != 3:
        raise IntegrationError("reviewer identities must be pairwise distinct")


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


def derive_snapshot_review_contracts(root: Path) -> dict[str, dict[str, Any]]:
    """Bind each external review hook to an exact, complete artifact set."""

    inventory = reviewable_snapshot_files(root)
    selectors: dict[str, tuple[str, ...]] = {
        "H-VALIDATE-HIDDEN-FIXTURE-MANIFESTS": (
            "freeze/fixtures/",
            "freeze/controls",
            "static/materialized/targets/",
            "targets.json",
        ),
        "H-VALIDATE-ORACLE-COVERAGE": (
            "freeze/oracle/",
            "freeze/atoms/",
            "freeze/allowlists/",
            "freeze/rules/",
            "freeze/authority/",
        ),
        "H-VALIDATE-INDEPENDENT-SIGNOFFS": ("freeze/reviews/",),
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
        contract = {
            "schema_version": 1,
            "status": "READY",
            "hook_id": hook_id,
            "procedure_id": f"v5-snapshot-review/{hook_id.lower()}",
            "procedure_version": SNAPSHOT_REVIEW_PROCEDURE_VERSION,
            "custody_requirement": "VERIFIED_PRIVATE_COPY_AND_END_REVERIFY",
            "required_check_ids": list(SNAPSHOT_REVIEW_CHECK_IDS),
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
) -> dict[str, Any]:
    """Validate the stable v2 receipt contract shared with ``protocol.py``."""

    receipt = exact_object(
        value,
        {
            "schema_version",
            "status",
            "phase",
            "hook_id",
            "receipt_kind",
            "actor",
            "input_digests",
            "output_digests",
            "result",
        },
        f"receipt {expected_hook_id}",
    )
    if (
        receipt["schema_version"] != 2
        or receipt["status"] != "PASS"
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


def snapshot_receipt_inputs(root: Path, hook_id: str) -> dict[str, str]:
    inputs = {
        SNAPSHOT_DESCRIPTOR: sha256((root / SNAPSHOT_DESCRIPTOR).read_bytes()),
        SNAPSHOT_MANIFEST: sha256((root / SNAPSHOT_MANIFEST).read_bytes()),
    }
    contract_path = f"static/integration/review-contracts/{hook_id}.json"
    inputs[contract_path] = sha256((root / contract_path).read_bytes())
    return inputs


def validate_snapshot_review_receipt(
    path: Path,
    expected_hook: str,
    snapshot: Path,
    descriptor: dict[str, Any],
) -> dict[str, Any]:
    receipt = validate_integration_receipt(
        read_json(path),
        expected_hook_id=expected_hook,
        expected_phase="SNAPSHOT_REVIEW",
    )
    contract = validate_snapshot_review_contracts(snapshot)[expected_hook]
    if receipt["input_digests"] != snapshot_receipt_inputs(snapshot, expected_hook):
        raise IntegrationError(
            f"snapshot review does not bind the exact snapshot: {expected_hook}"
        )
    if receipt["output_digests"] != {
        "reviewed-payload-manifest": descriptor["payload_manifest_sha256"],
        "reviewed-artifact-set": contract["artifact_set_sha256"],
    }:
        raise IntegrationError(
            f"snapshot review output does not identify the reviewed payload: {expected_hook}"
        )
    actor = receipt["actor"]
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
            contract["procedure_version"],
        ),
        "ARTIFACT-INVENTORY-CHECKED": (contract["artifact_set_sha256"],),
        "HOOK-SEMANTICS-CHECKED": (expected_hook,),
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
        "contract_id": "v5-evaluator-runtime-instantiation-v1",
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


def validate_word_counter(source_path: Path) -> dict[str, Any]:
    if source_path.is_symlink() or not source_path.is_file():
        raise IntegrationError("staged word counter must be a regular file")
    source_bytes = source_path.read_bytes()
    module = types.ModuleType("_v5_exact_staged_word_counter")
    module.__file__ = str(source_path)
    try:
        code = compile(source_bytes, str(source_path), "exec", dont_inherit=True)
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


def copy_snapshot_review_receipts(
    stage: Path,
    snapshot: Path,
    receipts: Path,
    descriptor: dict[str, Any],
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
    for hook_id in sorted(EXTERNAL_REVIEW_HOOKS):
        source = receipts / f"{hook_id}.json"
        validate_snapshot_review_receipt(source, hook_id, snapshot, descriptor)
        data = source.read_bytes()
        destination = stage / "static" / "integration-receipts" / source.name
        write_exclusive(destination, data)
        result[hook_id] = sha256(data)
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

    if bundle_kind == "PRODUCTION":
        for name in ("integrate.py", "prepare.py", "protocol.py", "word_count.py"):
            if (root / name).read_bytes() != (RUN / name).read_bytes():
                raise IntegrationError(
                    f"PRODUCTION snapshot {name} differs from the trusted verifier bytes"
                )
    for name in (
        "gate-manifest.json",
        "root-inventory.json",
        "aggregation-rules.json",
        "comparison-predicate.json",
        "report-projection-contract.json",
        "materiality-review-contract.json",
    ):
        value = read_json(root / name)
        if not isinstance(value, dict) or value.get("status") != "READY":
            raise IntegrationError(f"promoted operational contract is not READY: {name}")
    declaration_bytes = (root / "static" / "integration" / "source-declaration.json").read_bytes()
    if bundle_kind == "PRODUCTION" and declaration_bytes != trusted_production_declaration_bytes():
        raise IntegrationError(
            "PRODUCTION snapshot does not embed the exact trusted source declaration bytes"
        )
    declaration = validate_source_declaration(
        parse_json_bytes(declaration_bytes, "locked source declaration"),
        production=bundle_kind == "PRODUCTION",
    )
    values_bytes = (root / "static" / "integration" / "integration-values.json").read_bytes()
    values = validate_reviewed_values(
        parse_json_bytes(values_bytes, "locked integration values"), declaration_bytes
    )
    validate_reviewed_static(root, values["reviewed_static"])
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
        if bundle_kind == "PRODUCTION"
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
        if bundle_kind == "PRODUCTION":
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
        if bundle_kind == "PRODUCTION":
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
    validate_report_material(
        root,
        documents,
        packages,
        targets,
        values,
        execution_digests,
        spec_digests,
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
) -> dict[str, Any]:
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
    lock = exact_object(
        read_json(lock_path),
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
    observed = {
        path.name for path in receipt_root.iterdir() if path.is_file() and path.name != "index.json"
    }
    if observed != {f"{hook_id}.json" for hook_id in EXTERNAL_REVIEW_HOOKS}:
        raise IntegrationError("locked snapshot-review receipt file inventory is not exact")
    if any(path.is_dir() for path in receipt_root.rglob("*")):
        raise IntegrationError("locked snapshot-review receipt root contains a directory")
    for hook_id, expected_sha in receipt_map.items():
        digest(expected_sha, f"lock receipt {hook_id}")
        receipt_path = receipt_root / f"{hook_id}.json"
        if sha256(receipt_path.read_bytes()) != expected_sha:
            raise IntegrationError(f"static lock receipt digest mismatch: {hook_id}")
        validate_snapshot_review_receipt(receipt_path, hook_id, root, descriptor)
    validate_hook_inventory(root, expected_status="READY")
    validate_runtime_policy(root, expected_status="READY")
    validate_integration_status(root, expected_bundle_kind=expected_bundle_kind)
    verify_final_permissions(root)
    return lock


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

    if expected_bundle_kind == "PRODUCTION" and expected_external_commitment is None:
        raise IntegrationError(
            "PRODUCTION verification requires a separately custodied external commitment"
        )
    lock = _verify_static_contents(root, expected_bundle_kind=expected_bundle_kind)
    if expected_external_commitment is not None:
        verify_external_static_commitment(root, expected_external_commitment)
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
    return _verify_static_contents(root, expected_bundle_kind=expected_bundle_kind)


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

    source_descriptor = verify_review_snapshot(
        snapshot.resolve(), expected_candidate_kind="PRODUCTION"
    )
    private_descriptor = verify_review_snapshot(
        private_copy.resolve(), expected_candidate_kind="PRODUCTION"
    )
    if source_descriptor != private_descriptor:
        raise IntegrationError("source snapshot and private review copy no longer agree")
    if snapshot_manifest_bytes(snapshot.resolve()) != snapshot_manifest_bytes(
        private_copy.resolve()
    ):
        raise IntegrationError("source snapshot and private review copy payloads differ")
    return private_descriptor


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
    production_declaration = bundle_kind == "PRODUCTION"
    if production_declaration and declaration_bytes != trusted_production_declaration_bytes():
        raise IntegrationError(
            "PRODUCTION preparation source declaration changed from trusted bytes"
        )
    declaration = validate_source_declaration(
        parse_json_bytes(declaration_bytes, str(declaration_path)),
        production=production_declaration,
    )
    if production_declaration and source_root != trusted_unsafe_rust_root():
        raise IntegrationError(
            "production source declaration requires the exact unsafe-rust source root"
        )
    reviewed_path = inputs / "reviewed-values.json"
    reviewed_bytes = reviewed_path.read_bytes()
    reviewed = validate_reviewed_values(
        parse_json_bytes(reviewed_bytes, str(reviewed_path)), declaration_bytes
    )
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
        validate_hook_inventory(stage, expected_status="READY")
        validate_runtime_policy(stage, expected_status="READY")
        validate_reviewed_static(stage, reviewed["reviewed_static"])

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
        build_prompts_and_launches(
            stage,
            documents,
            packages,
            targets,
            reviewed,
            workspace_base,
            execution_digests,
            spec_digests,
        )
        build_evaluator_material(stage, documents, execution_digests, spec_digests)
        write_json(
            stage / "static" / "integration" / "word-counter-binding.json",
            validate_word_counter(stage / "word_count.py"),
        )
        (stage / RUNTIME_STATE).mkdir(parents=True)
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
        make_tree_writable(stage)
        staged_descriptor = verify_review_snapshot(
            stage, expected_candidate_kind=bundle_kind
        )
        if staged_descriptor != descriptor:
            raise IntegrationError("snapshot descriptor changed while copying for finalization")
        receipt_map = copy_snapshot_review_receipts(
            stage, stage, receipts, staged_descriptor
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
        publish_no_replace(stage, output)
        _verify_static_precommit(
            output,
            expected_bundle_kind=bundle_kind,
            capability=_FINALIZATION_PRECOMMIT_CAPABILITY,
        )
        commitment = _derive_external_static_commitment(output)
        if external_commitment_output is not None:
            _publish_external_commitment_file(external_commitment_output, commitment)
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
            "token_budget": 1000,
            "time_budget_seconds": 60,
            "tools": ["read"],
            "network_access": "DENIED",
            "documentation_access": "MOUNTED_ONLY",
            "hosted_build": "UNKNOWN_HOSTED_BUILD",
        }
        for role in ROLE_NAMES
    }


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


def build_synthetic_reviewed_overlay(inputs: Path) -> list[dict[str, Any]]:
    overlay = inputs / "reviewed-static"
    review_kinds = {
        "freeze/reviews/oracle-review-1.json": ("INDEPENDENT_ORACLE", "synthetic-oracle-1"),
        "freeze/reviews/oracle-review-2.json": ("INDEPENDENT_ORACLE", "synthetic-oracle-2"),
        "freeze/reviews/coherence-review.json": ("COHERENCE", "synthetic-coherence"),
    }
    for path_text in sorted(required_review_paths()):
        destination = overlay / path_text
        destination.parent.mkdir(parents=True, exist_ok=True)
        if path_text in review_kinds:
            review_kind, reviewer_id = review_kinds[path_text]
            destination.write_bytes(
                pretty_json_bytes(
                    {
                        "schema_version": 1,
                        "status": "READY",
                        "review_kind": review_kind,
                        "reviewer_id": reviewer_id,
                        "decision": "PASS",
                        "input_digests": {"synthetic-reviewed-scope": sha256(path_text.encode())},
                    }
                )
            )
            continue
        source = RUN / path_text
        if source.suffix == ".json":
            value = read_json(source)
            if (
                not isinstance(value, dict)
                or not isinstance(value.get("status"), str)
                or not value["status"].startswith("DRAFT")
            ):
                raise AssertionError(f"synthetic overlay source is not DRAFT JSON: {path_text}")
            destination.write_bytes(pretty_json_bytes({**value, "status": "READY"}))
        else:
            destination.write_bytes(source.read_bytes())
    return [
        {
            "path": path.relative_to(overlay).as_posix(),
            "sha256": sha256(path.read_bytes()),
            "decision": "PASS",
        }
        for path in sorted(overlay.rglob("*"))
        if path.is_file()
    ]


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
        inputs = snapshot_receipt_inputs(snapshot, hook_id)
        receipt = {
            "schema_version": 2,
            "status": "PASS",
            "phase": "SNAPSHOT_REVIEW",
            "hook_id": hook_id,
            "receipt_kind": "INDEPENDENT_SNAPSHOT_REVIEW",
            "actor": {
                "identity": f"synthetic-independent-reviewer-{index:02d}",
                "role": "INDEPENDENT_REVIEWER",
                "implementation": contract["procedure_id"],
                "version": contract["procedure_version"],
            },
            "input_digests": inputs,
            "output_digests": {
                "reviewed-payload-manifest": descriptor["payload_manifest_sha256"],
                "reviewed-artifact-set": contract["artifact_set_sha256"],
            },
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
                            f"{inputs[contract_path]}."
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
                            "to every contracted artifact."
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
            receipt_path, hook_id, snapshot, descriptor
        )


def expect_integration_failure(operation: Callable[[], Any], message: str) -> None:
    try:
        operation()
    except IntegrationError:
        return
    raise AssertionError(message)


def self_test() -> None:
    draft()
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
        reviewed_static = build_synthetic_reviewed_overlay(inputs)
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

        production_inputs = temp / "production-inputs"
        production_inputs.mkdir()
        (production_inputs / "authority.json").write_text(
            '{"production_test":"neutral authority"}\n', encoding="utf-8"
        )
        production_reviewed_static = build_synthetic_reviewed_overlay(
            production_inputs
        )
        production_declaration_bytes = trusted_production_declaration_bytes()
        production_reviewed = {
            "schema_version": 1,
            "status": "READY",
            "source_declaration_sha256": sha256(production_declaration_bytes),
            "authority_packet_path": "authority.json",
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
            "reviewed_static": production_reviewed_static,
        }
        (production_inputs / "reviewed-values.json").write_bytes(
            pretty_json_bytes(production_reviewed)
        )
        (production_inputs / "seeds.json").write_bytes(pretty_json_bytes(seeds))
        production_snapshot = temp / "production-review-snapshot"
        production_workspace = Path("/tmp") / sha256(
            f"production-{temp}".encode()
        )
        prepare_snapshot(
            source_root=trusted_unsafe_rust_root(),
            inputs=production_inputs,
            output=production_snapshot,
            workspace_base=production_workspace,
        )
        production_private_copy = temp / "production-private-review-copy"
        prepare_private_review_copy(production_snapshot, production_private_copy)
        verify_private_review_custody(
            production_snapshot, production_private_copy
        )
        production_receipts = temp / "production-receipts"
        write_synthetic_snapshot_receipts(
            production_snapshot,
            production_receipts,
            candidate_kind="PRODUCTION",
        )
        production_output = temp / "production-bundle"
        production_commitment_path = temp / "production-external-commitment.json"
        production_commitment = finalize_snapshot(
            snapshot=production_snapshot,
            receipts=production_receipts,
            output=production_output,
            external_commitment_output=production_commitment_path,
        )
        if read_json(production_commitment_path) != production_commitment:
            raise AssertionError("finalizer did not write its exact external commitment")
        verify_static(
            production_output,
            expected_bundle_kind="PRODUCTION",
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
            "public verifier accepted PRODUCTION without an external commitment",
        )
        wrong_production_commitment = {
            **production_commitment,
            "static_lock_sha256": "0" * 64,
        }
        expect_integration_failure(
            lambda: verify_static(
                production_output,
                expected_bundle_kind="PRODUCTION",
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

        # Model interruption after bundle publication but before commitment
        # publication: only the private recovery operation may bridge this gap.
        recovery_output = temp / "production-bundle-needing-recovery"
        _finalize_snapshot(
            snapshot=production_snapshot,
            receipts=production_receipts,
            output=recovery_output,
            bundle_kind="PRODUCTION",
            synthetic_capability=None,
        )
        recovery_commitment_path = temp / "recovered-external-commitment.json"
        expect_integration_failure(
            lambda: recover_external_commitment(
                root=recovery_output,
                output=recovery_commitment_path,
                custody_acknowledgement="",
            ),
            "recovery accepted no continuity-of-custody acknowledgement",
        )
        if os.path.lexists(recovery_commitment_path):
            raise AssertionError("failed recovery created a commitment")
        expect_integration_failure(
            lambda: recover_external_commitment(
                root=recovery_output,
                output=recovery_output / "candidate-local-commitment.json",
                custody_acknowledgement=RECOVERY_CUSTODY_ACKNOWLEDGEMENT,
            ),
            "recovery accepted a commitment output inside the bundle",
        )
        existing_recovery_path = temp / "existing-recovery-output.json"
        existing_recovery_path.write_bytes(b"already present\n")
        expect_integration_failure(
            lambda: recover_external_commitment(
                root=recovery_output,
                output=existing_recovery_path,
                custody_acknowledgement=RECOVERY_CUSTODY_ACKNOWLEDGEMENT,
            ),
            "recovery replaced an existing output",
        )
        recovered_commitment = recover_external_commitment(
            root=recovery_output,
            output=recovery_commitment_path,
            custody_acknowledgement=RECOVERY_CUSTODY_ACKNOWLEDGEMENT,
        )
        if (
            read_json(recovery_commitment_path) != recovered_commitment
            or stat.S_IMODE(
                recovery_commitment_path.stat(follow_symlinks=False).st_mode
            )
            != 0o444
        ):
            raise AssertionError("trusted recovery did not publish its exact read-only commitment")
        verify_static(
            recovery_output,
            expected_bundle_kind="PRODUCTION",
            expected_external_commitment=recovered_commitment,
        )
        expect_integration_failure(
            lambda: recover_external_commitment(
                root=recovery_output,
                output=recovery_commitment_path,
                custody_acknowledgement=RECOVERY_CUSTODY_ACKNOWLEDGEMENT,
            ),
            "recovery replaced an already recovered commitment",
        )

        trusted_protocol = __import__("protocol")
        verified_production, _ = trusted_protocol.load_verified_static_bundle(
            production_output, production_commitment_path
        )
        if verified_production != production_output:
            raise AssertionError("trusted protocol returned the wrong production root")
        ready_documents = trusted_protocol.load_ready_generated_documents(
            production_output
        )
        if (
            len(ready_documents["report-launch-records"]) != 120
            or len(
                ready_documents["evaluator-launch-contracts"]["assignments"]
            )
            != 43
        ):
            raise AssertionError(
                "trusted protocol did not accept the exact report/evaluator derivations"
            )
        if trusted_protocol.require_state_root(
            production_output / RUNTIME_STATE,
            static_root=production_output,
            external_commitment_path=production_commitment_path,
        ) != production_output / RUNTIME_STATE:
            raise AssertionError("trusted protocol returned the wrong bound state root")

        def expect_protocol_failure(operation: Callable[[], Any], message: str) -> None:
            try:
                operation()
            except trusted_protocol.ProtocolError:
                return
            raise AssertionError(message)

        expect_protocol_failure(
            lambda: trusted_protocol.load_verified_static_bundle(production_output),
            "trusted protocol accepted production without an external commitment",
        )
        expect_protocol_failure(
            lambda: trusted_protocol.require_state_root(
                production_output / RUNTIME_STATE,
                static_root=production_output,
            ),
            "trusted protocol accepted production state without a commitment",
        )
        expect_protocol_failure(
            lambda: trusted_protocol.require_state_root(
                production_output / RUNTIME_STATE,
                static_root=output,
                external_commitment_path=production_commitment_path,
            ),
            "trusted protocol accepted state bound to a mismatched static root",
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
    print("V5 snapshot/review/finalize synthetic self-test passed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    commands.add_parser("draft", help="validate the unsealed source and mechanism")
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
