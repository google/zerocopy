#!/usr/bin/env python3
"""Validate the eight hidden V5 fixture manifests and DRAFT bindings."""

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
PROMPT_SET_SENTINEL = "INTEGRATION_BOUND_EXACT_PROMPT_SET_SHA256"
HEX64 = re.compile(r"^[0-9a-f]{64}$")
ATOM_ID = re.compile(r"(?<![A-Z0-9])[EVFPBLRQ][1-9][0-9]*(?![0-9])")
TOP_KEYS = {
    "schema_version",
    "status",
    "mode",
    "prompt_regime",
    "neutral_label",
    "source_digest",
    "exact_prompt_set_sha256",
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
    "source_digest",
    "exact_prompt_set_sha256",
    "theorem_boundary_class",
    "witness_requirement",
    "case_control_class",
    "contamination_risk",
    "tcb_vacuity",
    "scorer_expertise",
    "scorer_version",
}


def load_json(path: Path) -> object:
    with path.open(encoding="utf-8") as source:
        return json.load(source)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> None:
    paths = sorted(FIXTURES_DIR.glob("*.json"), key=lambda path: path.name)
    require({path.stem for path in paths} == set(MODES), "fixture manifest filenames must be exactly E,V,F,P,B,L,R,Q")

    statuses: set[str] = set()
    labels: set[str] = set()
    documents: dict[str, dict[str, object]] = {}
    integration_bound: list[str] = []

    for path in paths:
        document = load_json(path)
        require(isinstance(document, dict) and set(document) == TOP_KEYS, f"{path}: fields are not exact")
        mode = path.stem
        require(document["schema_version"] == 1, f"{path}: schema_version must be 1")
        require(document["status"] in ("DRAFT", "READY"), f"{path}: invalid status")
        require(document["mode"] == mode, f"{path}: mode/filename mismatch")
        require(document["prompt_regime"] == REGIMES[mode], f"{path}: prompt regime/mode mismatch")
        require(document["neutral_label"] == LABELS[mode], f"{path}: wrong stable neutral label")
        require(document["neutral_label"] not in labels, f"{path}: duplicate neutral label")
        labels.add(document["neutral_label"])
        statuses.add(document["status"])

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

        source_digest = document["source_digest"]
        prompt_set_digest = document["exact_prompt_set_sha256"]
        if document["status"] == "DRAFT":
            require(source_digest == SOURCE_SENTINEL, f"{path}: DRAFT source digest must remain explicitly integration-bound")
            require(prompt_set_digest == PROMPT_SET_SENTINEL, f"{path}: DRAFT prompt-set digest must remain explicitly integration-bound")
            integration_bound.extend([f"{mode}.source_digest", f"{mode}.exact_prompt_set_sha256"])
        else:
            require(HEX64.fullmatch(source_digest) is not None, f"{path}: READY source digest must be SHA-256")
            require(source_digest != "0" * 64, f"{path}: READY source digest cannot be the all-zero sentinel")
            require(HEX64.fullmatch(prompt_set_digest) is not None, f"{path}: READY prompt-set digest must be SHA-256")
            require(prompt_set_digest != "0" * 64, f"{path}: READY prompt-set digest cannot be all zero")

        documents[mode] = document

    require(len(statuses) == 1, f"hidden fixture manifest statuses must advance atomically, got {sorted(statuses)}")

    controls = load_json(FREEZE / "controls.json")
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


if __name__ == "__main__":
    main()
