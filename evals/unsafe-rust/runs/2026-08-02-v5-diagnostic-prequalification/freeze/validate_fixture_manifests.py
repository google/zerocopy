#!/usr/bin/env python3
"""Validate hidden V5 manifests across source-review and snapshot phases."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


FREEZE = Path(__file__).resolve().parent
FIXTURES_DIR = FREEZE / "fixtures"
MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
LABELS = {
    "E": "fixture-alder",
    "V": "fixture-birch",
    "F": "fixture-cedar",
    "P": "fixture-dogwood",
    "B": "fixture-elm",
    "L": "fixture-fir",
    "R": "fixture-ginkgo",
    "Q": "fixture-hawthorn",
}
FIXTURE_IDS = {
    "E": "e_semantics",
    "V": "v_valid_use",
    "F": "f_fanout",
    "P": "p_predicates",
    "B": "b_build",
    "L": "l_proof",
    "R": "r_redesign",
    "Q": "q_metamorphic",
}
REGIMES = {
    "E": "CONTROLLED",
    "V": "CONTROLLED",
    "F": "CONTROLLED",
    "P": "CONTROLLED",
    "B": "NATURALISTIC",
    "L": "NATURALISTIC",
    "R": "NATURALISTIC",
    "Q": "CONTROLLED",
}
SOURCE_SENTINEL = "INTEGRATION_BOUND_SOURCE_TREE_SHA256"
REPORT_MATERIAL_SENTINEL = "INTEGRATION_BOUND_EXACT_REPORT_MATERIAL_SET_SHA256"
REVIEWED_DERIVATION_SENTINEL = "DERIVE_DURING_SNAPSHOT_BUILD"
SOURCE_TREE_ALGORITHM = "BYTE_TREE_V1"
REPORT_MATERIAL_SET_ALGORITHM = "V5_MODE_REPORT_MATERIAL_SET_V1"
HEX64 = re.compile(r"^[0-9a-f]{64}$")
ATOM_ID = re.compile(r"(?<![A-Za-z0-9_])[EVFPBLRQ][1-9][0-9]*(?![A-Za-z0-9_])")
COMMON_TOP_KEYS = {
    "schema_version",
    "status",
    "mode",
    "prompt_regime",
    "neutral_label",
    "source_tree_algorithm",
    "source_tree_sha256",
    "report_material_set_algorithm",
    "exact_report_material_set_sha256",
    "scoped_surfaces",
    "theorem_boundary_class",
    "supported_set",
    "trigger_set",
    "alternative_proof_paths",
    "witness_requirement",
    "case_control_class",
    "contamination_risk",
    "claim_layers",
    "tcb_vacuity",
    "permissions",
    "scorer_expertise",
    "scorer_version",
    "retirement_triggers",
}
P_REUSE_KEY = "reused_fixture_binding"
P_REUSE_BINDING = {
    "evidence_class": "EXPOSED_PRIOR_RUN_REGRESSION_ONLY",
    "fixture_source_path": "fixtures/v4-focused/p_predicates",
    "source_tree_algorithm": "BYTE_TREE_V1",
    "source_tree_sha256": "2b194a735b69a8904b86baa43791a0ddac9f769ce32e87bf4e759822cb5cd52e",
    "lineage_run_path": "runs/2026-08-01-v4-focused",
    "target_label": "m4",
    "target_map_path": "runs/2026-08-01-v4-focused/sealed/target-map.tsv",
    "target_map_sha256": "f1c89a72bf11c705e04fa576d0a7979e24799ca1f714def6b4db6bd0a06d5837",
    "lock_path": "runs/2026-08-01-v4-focused/freeze/LOCK.json",
    "lock_sha256": "cd7a300f83b045f76530eded20ec2d22bd6abbd484d6459ff50245fb07ef943e",
    "file_manifest_path": "runs/2026-08-01-v4-focused/freeze/file-manifest.sha256",
    "file_manifest_sha256": "059cde170e6e31d4ef4c4997b4a64413fdd9e47e9f9e5df74c1c9707bf6e3c58",
    "authority_manifest_path": "runs/2026-08-01-v4-focused/freeze/authority-manifest.tsv",
    "authority_manifest_sha256": "48444682cfc13966ce2769add9d4fbde82426a7a6e8777c421be8b26d15ff293",
    "rubric_path": "runs/2026-08-01-v4-focused/freeze/rubrics/P.md",
    "rubric_sha256": "1e9e6622a34b3b0376b6912f676695e318edcd971ac1f4960810531ad854911d",
}
PERMISSIONS = {
    "target_access": "DECLARED_INPUTS_READ_ONLY",
    "modification": "FORBIDDEN",
    "build_run_test": "FORBIDDEN",
    "network": "FORBIDDEN",
    "authority_access": "AGENT_VISIBLE_NEUTRAL_ONLY",
    "evaluator_only_material": "FORBIDDEN",
}
ARRAY_FIELDS = {
    "scoped_surfaces",
    "supported_set",
    "trigger_set",
    "alternative_proof_paths",
    "claim_layers",
    "retirement_triggers",
}
STRING_FIELDS = {
    "neutral_label",
    "source_tree_algorithm",
    "source_tree_sha256",
    "report_material_set_algorithm",
    "exact_report_material_set_sha256",
    "theorem_boundary_class",
    "witness_requirement",
    "case_control_class",
    "contamination_risk",
    "tcb_vacuity",
    "scorer_expertise",
    "scorer_version",
}
EXPECTED_SCOPED_SURFACES = {
    "E": (
        "e_semantics/Cargo.toml",
        "e_semantics/src/lib.rs::record",
        "e_semantics/src/lib.rs::last_or",
        "e_semantics/src/lib.rs::boundary_or",
        "e_semantics/src/lib.rs::configured_lane",
        "e_semantics/REQUEST.md",
        "e_semantics/SUPPORT.md",
        "e_semantics/TCB.md::CONFIG-MAP",
    ),
    "V": (
        "v_valid_use/Cargo.toml",
        "v_valid_use/src/lib.rs::Slot",
        "v_valid_use/src/lib.rs::Slot::index",
        "v_valid_use/src/lib.rs::choose",
        "v_valid_use/src/lib.rs::Anchor",
        "v_valid_use/src/lib.rs::<Anchor as Slot>::index",
        "v_valid_use/src/lib.rs::owned",
        "v_valid_use/caller_examples.rs::East",
        "v_valid_use/caller_examples.rs::<East as Slot>::index",
        "v_valid_use/caller_examples.rs::example_east",
        "v_valid_use/caller_examples.rs::West",
        "v_valid_use/caller_examples.rs::<West as Slot>::index",
        "v_valid_use/caller_examples.rs::example_west",
        "v_valid_use/REQUEST.md",
        "v_valid_use/SUPPORT.md",
    ),
    "F": (
        "f_fanout/Cargo.toml",
        "f_fanout/src/lib.rs::staged_token",
        "f_fanout/src/lib.rs::staged_value",
        "f_fanout/src/lib.rs::staged_is_nonzero",
        "f_fanout/src/lib.rs::local_token",
        "f_fanout/src/lib.rs::checked_token",
        "f_fanout/DEPENDENCY-API.md",
        "f_fanout/REQUEST.md",
        "f_fanout/SUPPORT.md",
        "f_fanout/TCB.md",
    ),
    "P": (
        "p_predicates/Cargo.toml",
        "p_predicates/src/lib.rs::value_or_zero",
        "p_predicates/src/lib.rs::turbo-wasm32 compile_error",
        "p_predicates/POLICY-SCARLET.md",
        "p_predicates/POLICY-INDIGO.md",
        "p_predicates/REQUEST.md",
        "p_predicates/TCB.md::BUILD-MAP-POLICY",
    ),
    "B": (
        "b_build/Cargo.toml",
        "b_build/build.rs",
        "b_build/src/lib.rs::lane_id",
        "b_build/src/lib.rs::wasm32-arena compile_error",
        "b_build/BUILD.md",
        "b_build/SUPPORT.md",
        "b_build/TCB.md::BUILD-MAP-ORDERED",
        "b_build/REQUEST.md",
    ),
    "L": (
        "l_proof/lib.rs::last",
        "l_proof/lib.rs::last SAFETY comment",
        "l_proof/REQUEST.md",
    ),
    "R": (
        "r_redesign/lib.rs::Slot",
        "r_redesign/lib.rs::Slot::index",
        "r_redesign/lib.rs::Tail",
        "r_redesign/lib.rs::<Tail as Slot>::index",
        "r_redesign/lib.rs::increment",
        "r_redesign/REQUEST.md::Design review request",
    ),
    "Q": (
        "q_metamorphic/Cargo.toml",
        "q_metamorphic/src/lib.rs::LOCAL_ENTRY_B",
        "q_metamorphic/src/lib.rs::local_text",
        "q_metamorphic/src/lib.rs::catalog_text",
        "q_metamorphic/src/lib.rs::delegated_text",
        "q_metamorphic/caller_examples.rs::PEER_INPUT_A",
        "q_metamorphic/caller_examples.rs::PEER_INPUT_B",
        "q_metamorphic/caller_examples.rs::example_local",
        "q_metamorphic/caller_examples.rs::example_peer_a",
        "q_metamorphic/caller_examples.rs::example_peer_b",
        "q_metamorphic/DEPENDENCY-API.md",
        "q_metamorphic/REQUEST.md",
        "q_metamorphic/SUPPORT.md",
        "q_metamorphic/TCB.md",
    ),
}
PUBLIC_RUST_ITEM = re.compile(
    r'^\s*pub(?:\s*\([^\n)]*\))?\s+'
    r'(?:(?:unsafe|async|const)\s+)*(?:extern\s+"[^"]+"\s+)?'
    r'(?:fn|trait|struct|enum|union|type|static|const|mod|macro)\s+(r#[A-Za-z_][A-Za-z0-9_]*|[A-Za-z_][A-Za-z0-9_]*)',
    flags=re.MULTILINE,
)
PUBLIC_RUST_USE = re.compile(r"^\s*pub(?:\s*\([^\n)]*\))?\s+use\b", flags=re.MULTILINE)
PUBLIC_RUST_FIELD = re.compile(
    r"^\s*pub(?:\s*\([^\n)]*\))?\s+(?:r#)?[A-Za-z_][A-Za-z0-9_]*\s*:",
    flags=re.MULTILINE,
)
EXPORTED_MACRO = re.compile(
    r"#\s*\[\s*macro_export(?:\([^]]*\))?\s*]\s*macro_rules!\s*([A-Za-z_][A-Za-z0-9_]*)",
    flags=re.MULTILINE,
)


def named_block(text: str, header: re.Pattern[str]) -> str | None:
    """Return a simple Rust item's brace-delimited body, if present."""
    match = header.search(text)
    if match is None:
        return None
    opening = text.find("{", match.end() - 1)
    if opening < 0:
        return None
    depth = 0
    for index in range(opening, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[opening + 1 : index]
    return None


def rust_item_pattern(name: str) -> re.Pattern[str]:
    escaped = re.escape(name.removeprefix("r#"))
    return re.compile(
        rf"\b(?:fn|trait|struct|enum|union|type|static|const|mod|macro_rules!)\s+(?:r#)?{escaped}\b"
    )


def validate_rust_selector(selector: str, text: str, surface: str) -> None:
    if selector.endswith(" compile_error"):
        condition = selector.removesuffix(" compile_error")
        require("compile_error!" in text, f"{surface}: named compile_error is absent")
        require(
            all(re.search(rf"\b{re.escape(term)}\b", text) for term in condition.split("-")),
            f"{surface}: named compile_error condition is absent",
        )
        return

    if selector.endswith(" SAFETY comment"):
        item = selector.removesuffix(" SAFETY comment")
        body = named_block(text, re.compile(rf"\bfn\s+(?:r#)?{re.escape(item)}\b"))
        require(body is not None, f"{surface}: named function is absent")
        require(re.search(r"//\s*SAFETY\s*:", body) is not None, f"{surface}: named SAFETY comment is absent")
        return

    trait_impl = re.fullmatch(
        r"<(?P<type>(?:r#)?[A-Za-z_][A-Za-z0-9_]*) as "
        r"(?P<trait>(?:r#)?[A-Za-z_][A-Za-z0-9_]*)>::"
        r"(?P<method>(?:r#)?[A-Za-z_][A-Za-z0-9_]*)",
        selector,
    )
    if trait_impl is not None:
        type_name = trait_impl.group("type")
        trait_name = trait_impl.group("trait")
        method_name = trait_impl.group("method")
        header = re.compile(
            rf"\b(?:unsafe\s+)?impl\s+{re.escape(trait_name)}\s+for\s+{re.escape(type_name)}\s*\{{"
        )
        body = named_block(text, header)
        require(body is not None, f"{surface}: named trait implementation is absent")
        require(rust_item_pattern(method_name).search(body) is not None, f"{surface}: named implementation method is absent")
        return

    associated = re.fullmatch(
        r"(?P<owner>(?:r#)?[A-Za-z_][A-Za-z0-9_]*)::"
        r"(?P<member>(?:r#)?[A-Za-z_][A-Za-z0-9_]*)",
        selector,
    )
    if associated is not None:
        owner = associated.group("owner")
        member = associated.group("member")
        trait_body = named_block(
            text,
            re.compile(rf"\b(?:unsafe\s+)?trait\s+{re.escape(owner)}\b[^{{]*\{{"),
        )
        impl_body = named_block(text, re.compile(rf"\bimpl\s+{re.escape(owner)}\b[^{{]*\{{"))
        body = trait_body if trait_body is not None else impl_body
        require(body is not None, f"{surface}: named trait or inherent implementation is absent")
        require(rust_item_pattern(member).search(body) is not None, f"{surface}: named associated item is absent")
        return

    require(rust_item_pattern(selector).search(text) is not None, f"{surface}: named Rust item is absent")


def validate_surface_selector(surface: str, fixture_root: Path) -> None:
    relative, separator, selector = surface.partition("::")
    if not separator:
        return
    path = fixture_root.parent / relative
    text = path.read_text(encoding="utf-8")
    if path.suffix == ".rs":
        validate_rust_selector(selector, text, surface)
    else:
        heading = re.compile(rf"^\s*#+\s+{re.escape(selector)}\s*$", flags=re.MULTILINE | re.IGNORECASE)
        require(heading.search(text) is not None, f"{surface}: named document section is absent")


def reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
    result: dict[str, object] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def reject_nonfinite_number(token: str) -> object:
    raise ValueError(f"non-finite JSON number: {token}")


def parse_json_bytes(raw: bytes, label: object = "JSON input") -> object:
    try:
        text = raw.decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{label}: not strict UTF-8") from error
    return json.loads(
        text,
        object_pairs_hook=reject_duplicate_keys,
        parse_constant=reject_nonfinite_number,
    )


def load_json(path: Path) -> object:
    return parse_json_bytes(path.read_bytes(), path)


def byte_tree_v1(root: Path) -> str:
    """Recompute the historical source-tree identity bound by V4 and V5."""
    require(root.is_dir() and not root.is_symlink(), f"BYTE_TREE_V1 root is not a real directory: {root}")
    records: list[bytes] = []
    for item in sorted(root.rglob("*"), key=lambda value: value.relative_to(root).as_posix()):
        relative = item.relative_to(root).as_posix()
        require(
            not item.is_symlink() and (item.is_dir() or item.is_file()),
            f"unsupported BYTE_TREE_V1 entry: {item}",
        )
        if item.is_dir():
            records.append(f"d\0{relative}\n".encode())
        else:
            data = item.read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            records.append(f"f\0{relative}\0{len(data)}\0{digest}\n".encode())
    return hashlib.sha256(b"".join(records)).hexdigest()


def validate_scoped_surfaces(
    mode: str,
    document: dict[str, object],
    fixture_root: Path,
    manifest_path: Path,
) -> None:
    surfaces = document["scoped_surfaces"]
    require(
        surfaces == list(EXPECTED_SCOPED_SURFACES[mode]),
        f"{manifest_path}: scoped_surfaces differ from the reviewed exact inventory",
    )
    actual_surfaces = {
        f"{FIXTURE_IDS[mode]}/{file.relative_to(fixture_root).as_posix()}"
        for file in fixture_root.rglob("*")
        if file.is_file()
    }
    declared_files = {surface.partition("::")[0] for surface in surfaces}
    require(
        declared_files == actual_surfaces,
        f"{manifest_path}: scoped_surfaces must cover every fixture file exactly; "
        f"missing={sorted(actual_surfaces - declared_files)} "
        f"extra={sorted(declared_files - actual_surfaces)}",
    )
    for surface in surfaces:
        validate_surface_selector(surface, fixture_root)

    # This deliberately checks public source syntax as well as the hand-reviewed
    # inventory. The exact inventory accounts for public-trait methods and
    # relevant private implementations. The scans prevent newly added safe API
    # syntax from silently escaping it and fail closed on surface forms for
    # which this manifest has no exact selector encoding.
    for rust_file in sorted(fixture_root.rglob("*.rs")):
        relative = rust_file.relative_to(fixture_root).as_posix()
        prefix = f"{FIXTURE_IDS[mode]}/{relative}::"
        text = rust_file.read_text(encoding="utf-8")
        require(PUBLIC_RUST_USE.search(text) is None, f"{manifest_path}: public use needs an exact surface encoding: {rust_file}")
        require(PUBLIC_RUST_FIELD.search(text) is None, f"{manifest_path}: public field needs an exact surface encoding: {rust_file}")
        for name in PUBLIC_RUST_ITEM.findall(text) + EXPORTED_MACRO.findall(text):
            direct_surface = prefix + name.removeprefix("r#")
            require(
                direct_surface in surfaces,
                f"{manifest_path}: public Rust surface missing exact inventory entry {direct_surface}",
            )
        for trait_name in re.findall(
            r"\bpub(?:\s*\([^\n)]*\))?\s+(?:unsafe\s+)?trait\s+((?:r#)?[A-Za-z_][A-Za-z0-9_]*)",
            text,
        ):
            body = named_block(
                text,
                re.compile(rf"\b(?:unsafe\s+)?trait\s+{re.escape(trait_name)}\b[^{{]*\{{"),
            )
            require(body is not None, f"{manifest_path}: cannot inventory public trait body {trait_name}")
            for method_name in re.findall(r"\bfn\s+((?:r#)?[A-Za-z_][A-Za-z0-9_]*)\b", body):
                direct_surface = prefix + trait_name.removeprefix("r#") + "::" + method_name.removeprefix("r#")
                require(
                    direct_surface in surfaces,
                    f"{manifest_path}: public trait method missing exact inventory entry {direct_surface}",
                )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def validate(
    freeze_root: Path = FREEZE,
    *,
    unsafe_rust_root: Path | None = None,
    expected_phase: str = "DRAFT",
    expected_source_digests: dict[str, str] | None = None,
    expected_report_material_digests: dict[str, str] | None = None,
) -> dict[str, dict[str, object]]:
    """Validate the same semantic closure at each honest lifecycle phase."""

    require(
        expected_phase in {"DRAFT", "SOURCE_REVIEW_CANDIDATE", "READY"},
        f"unknown fixture validation phase: {expected_phase}",
    )
    unsafe_rust = unsafe_rust_root or freeze_root.parents[2]
    fixtures_dir = freeze_root / "fixtures"
    paths = sorted(fixtures_dir.glob("*.json"), key=lambda path: path.name)
    require({path.stem for path in paths} == set(MODES), "fixture manifest filenames must be exactly E,V,F,P,B,L,R,Q")

    statuses: set[str] = set()
    labels: set[str] = set()
    documents: dict[str, dict[str, object]] = {}
    integration_bound: list[str] = []

    for path in paths:
        document = load_json(path)
        mode = path.stem
        expected_keys = COMMON_TOP_KEYS | ({P_REUSE_KEY} if mode == "P" else set())
        require(isinstance(document, dict) and set(document) == expected_keys, f"{path}: fields are not exact")
        require(document["schema_version"] == 1, f"{path}: schema_version must be 1")
        expected_status = {
            "DRAFT": "DRAFT",
            "SOURCE_REVIEW_CANDIDATE": "SOURCE-REVIEW-CANDIDATE",
            "READY": "READY",
        }[expected_phase]
        require(document["status"] == expected_status, f"{path}: status must be {expected_status}")
        require(document["mode"] == mode, f"{path}: mode/filename mismatch")
        require(document["prompt_regime"] == REGIMES[mode], f"{path}: prompt regime/mode mismatch")
        require(document["neutral_label"] == LABELS[mode], f"{path}: wrong stable neutral label")
        require(document["neutral_label"] not in labels, f"{path}: duplicate neutral label")
        labels.add(document["neutral_label"])
        statuses.add(document["status"])
        require(document["source_tree_algorithm"] == SOURCE_TREE_ALGORITHM, f"{path}: wrong source-tree algorithm")
        require(document["report_material_set_algorithm"] == REPORT_MATERIAL_SET_ALGORITHM, f"{path}: wrong report-material-set algorithm")

        for field in STRING_FIELDS:
            require(isinstance(document[field], str) and document[field].strip(), f"{path}: {field} must be nonblank")
        for field in ARRAY_FIELDS:
            values = document[field]
            require(isinstance(values, list), f"{path}: {field} must be an array")
            require(values or field == "alternative_proof_paths", f"{path}: {field} must be nonempty")
            require(all(isinstance(value, str) and value.strip() for value in values), f"{path}: blank/non-string {field}")
            require(len(values) == len(set(values)), f"{path}: duplicate {field}")
        require(document["permissions"] == PERMISSIONS, f"{path}: permissions are not exact")
        require(document["scorer_version"] == "v5-diagnostic-direct-decision-v1", f"{path}: wrong scorer version")
        require(not ATOM_ID.search(json.dumps(document, ensure_ascii=False)), f"{path}: must not duplicate atom-by-atom truth")

        fixture_collection = "v4-focused" if mode == "P" else "v5-diagnostic-prequalification"
        fixture_root = unsafe_rust / "fixtures" / fixture_collection / FIXTURE_IDS[mode]
        validate_scoped_surfaces(mode, document, fixture_root, path)

        if mode == "P":
            binding = document[P_REUSE_KEY]
            require(binding == P_REUSE_BINDING, f"{path}: reused V4 fixture binding is not exact")
            actual_tree_digest = byte_tree_v1(fixture_root)
            require(
                actual_tree_digest == binding["source_tree_sha256"],
                f"{path}: live reused fixture BYTE_TREE_V1 mismatch: "
                f"expected={binding['source_tree_sha256']} actual={actual_tree_digest}",
            )
            for path_key, digest_key in (
                ("target_map_path", "target_map_sha256"),
                ("lock_path", "lock_sha256"),
                ("file_manifest_path", "file_manifest_sha256"),
                ("authority_manifest_path", "authority_manifest_sha256"),
                ("rubric_path", "rubric_sha256"),
            ):
                lineage_path = unsafe_rust / binding[path_key]
                require(lineage_path.is_file(), f"{path}: missing lineage file {lineage_path}")
                actual_digest = hashlib.sha256(lineage_path.read_bytes()).hexdigest()
                require(actual_digest == binding[digest_key], f"{path}: lineage digest mismatch for {lineage_path}")
            target_row = "\t".join(
                [
                    binding["target_label"],
                    "P",
                    binding["fixture_source_path"],
                    binding["source_tree_sha256"],
                    "3000",
                ]
            )
            target_rows = (unsafe_rust / binding["target_map_path"]).read_text(encoding="utf-8").splitlines()
            require(target_row in target_rows, f"{path}: V4 target map does not bind the declared P source tree")

        source_digest = document["source_tree_sha256"]
        material_digest = document["exact_report_material_set_sha256"]
        if expected_phase == "DRAFT":
            require(source_digest == SOURCE_SENTINEL, f"{path}: DRAFT source digest must remain explicitly integration-bound")
            require(material_digest == REPORT_MATERIAL_SENTINEL, f"{path}: DRAFT report-material digest must remain explicitly integration-bound")
            integration_bound.extend([f"{mode}.source_tree_sha256", f"{mode}.exact_report_material_set_sha256"])
        else:
            require(expected_source_digests is not None and set(expected_source_digests) == set(MODES), "expected source digests must cover every mode")
            require(source_digest == expected_source_digests[mode], f"{path}: source-tree digest does not equal the trusted target")
            require(HEX64.fullmatch(source_digest) is not None and source_digest != "0" * 64, f"{path}: source-tree digest must be a nonzero SHA-256")
            if expected_phase == "SOURCE_REVIEW_CANDIDATE":
                require(material_digest == REVIEWED_DERIVATION_SENTINEL, f"{path}: source-review candidate must not claim review of not-yet-derived report material")
            else:
                require(expected_report_material_digests is not None and set(expected_report_material_digests) == set(MODES), "expected report-material digests must cover every mode")
                require(material_digest == expected_report_material_digests[mode], f"{path}: report-material digest does not equal the exact generated artifacts")
                require(HEX64.fullmatch(material_digest) is not None and material_digest != "0" * 64, f"{path}: report-material digest must be a nonzero SHA-256")

        documents[mode] = document

    require(len(statuses) == 1, f"hidden fixture manifest statuses must advance atomically, got {sorted(statuses)}")

    controls = load_json(freeze_root / "controls.json")
    expected_control_status = {
        "DRAFT": "DRAFT",
        "SOURCE_REVIEW_CANDIDATE": "SOURCE-REVIEW-CANDIDATE",
        "READY": "READY",
    }[expected_phase]
    require(
        controls.get("status") == expected_control_status,
        "controls status does not match fixture lifecycle phase",
    )
    control_modes = {mode: set() for mode in MODES}
    for control in controls["controls"]:
        control_modes[control["mode"]].add(control["family"])
        require(control["fixture_id"] == FIXTURE_IDS[control["mode"]], f"{control['id']}: hidden fixture/control fixture mismatch")
    for mode in MODES:
        require(control_modes[mode] == {"PROOF_QUALITY", "CLASSIFICATION_CONTROL"}, f"{mode}: controls do not cover both families")

    digest = hashlib.sha256(
        b"".join(path.name.encode("utf-8") + b"\0" + path.read_bytes() for path in paths)
    ).hexdigest()
    print(
        f"hidden fixture manifests ok: manifests={len(documents)} status={next(iter(statuses))} "
        f"integration_bound_fields={len(integration_bound)} aggregate_sha256={digest}"
    )
    if integration_bound:
        print("READY_BLOCKED_PENDING_INTEGRATION: " + ", ".join(integration_bound))
    return documents


def main() -> None:
    validate()


if __name__ == "__main__":
    main()
