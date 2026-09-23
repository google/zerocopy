#!/usr/bin/env python3
"""Validate the evaluator-only V5 control inventory and atom coverage."""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path


FREEZE = Path(__file__).resolve().parent
CONTROLS_PATH = FREEZE / "controls.json"
ATOMS_DIR = FREEZE / "atoms"

MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
FAMILIES = ("PROOF_QUALITY", "CLASSIFICATION_CONTROL")
FIXTURES = {
    "E": "e_semantics",
    "V": "v_valid_use",
    "F": "f_fanout",
    "P": "p_predicates",
    "B": "b_build",
    "L": "l_proof",
    "R": "r_redesign",
    "Q": "q_metamorphic",
}
TOP_KEYS = {"schema_version", "status", "controls"}
CONTROL_KEYS = {
    "id",
    "family",
    "mode",
    "fixture_id",
    "atom_ids",
    "applicability",
    "expected_relation",
    "rationale",
}
EXPECTED_RELATION = {
    "kind": "ALL_LISTED_ATOM_CERTIFICATES_EQUAL",
    "certificate_field": "certificate_decision",
    "expected_decision": "PASS",
}
ID_RE = re.compile(r"^(PQ|CC)-([EVFPBLRQ])-[A-Z0-9-]+$")
FAMILY_PREFIX = {
    "PROOF_QUALITY": "PQ",
    "CLASSIFICATION_CONTROL": "CC",
}


def load_json(path: Path) -> object:
    return parse_json_bytes(path.read_bytes(), path)


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


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def load_atoms(freeze_root: Path, expected_status: str) -> dict[str, str]:
    atom_modes: dict[str, str] = {}
    for mode in MODES:
        path = freeze_root / "atoms" / f"{mode}.json"
        document = load_json(path)
        require(isinstance(document, dict), f"{path}: root must be an object")
        require(document.get("schema_version") == 1, f"{path}: schema_version must be 1")
        require(document.get("status") == expected_status, f"{path}: status must be {expected_status}")
        require(document.get("mode") == mode, f"{path}: mode must be {mode}")
        atoms = document.get("atoms")
        require(isinstance(atoms, list), f"{path}: atoms must be an array")
        for atom in atoms:
            require(isinstance(atom, dict), f"{path}: every atom must be an object")
            atom_id = atom.get("id")
            require(isinstance(atom_id, str), f"{path}: every atom needs a string id")
            require(atom_id.startswith(mode), f"{path}: atom {atom_id} has the wrong mode prefix")
            require(atom_id not in atom_modes, f"duplicate atom id: {atom_id}")
            atom_modes[atom_id] = mode
    return atom_modes


def validate(freeze_root: Path = FREEZE, *, expected_status: str = "DRAFT") -> str:
    require(
        expected_status in {"DRAFT", "SOURCE-REVIEW-CANDIDATE", "READY"},
        "controls expected status is unknown",
    )
    atom_modes = load_atoms(freeze_root, expected_status)
    controls_path = freeze_root / "controls.json"
    raw_controls = controls_path.read_bytes()
    document = parse_json_bytes(raw_controls, controls_path)
    require(isinstance(document, dict), "controls.json: root must be an object")
    require(set(document) == TOP_KEYS, "controls.json: top-level fields are not exact")
    require(document["schema_version"] == 1, "controls.json: schema_version must be 1")
    require(document["status"] == expected_status, f"controls.json: status must be {expected_status}")
    controls = document["controls"]
    require(isinstance(controls, list) and controls, "controls.json: controls must be nonempty")

    seen_ids: set[str] = set()
    covered_atoms: set[str] = set()
    family_modes: set[tuple[str, str]] = set()
    signatures: set[tuple[str, str, tuple[str, ...]]] = set()
    family_counts = {family: 0 for family in FAMILIES}

    for index, control in enumerate(controls):
        label = f"controls[{index}]"
        require(isinstance(control, dict), f"{label}: must be an object")
        require(set(control) == CONTROL_KEYS, f"{label}: fields are not exact")

        control_id = control["id"]
        require(isinstance(control_id, str), f"{label}.id: must be a string")
        match = ID_RE.fullmatch(control_id)
        require(match is not None, f"{label}.id: invalid stable control id {control_id!r}")
        require(control_id not in seen_ids, f"duplicate control id: {control_id}")
        seen_ids.add(control_id)

        family = control["family"]
        mode = control["mode"]
        require(family in FAMILIES, f"{control_id}: unknown family {family!r}")
        require(mode in MODES, f"{control_id}: unknown mode {mode!r}")
        require(match.group(1) == FAMILY_PREFIX[family], f"{control_id}: id/family mismatch")
        require(match.group(2) == mode, f"{control_id}: id/mode mismatch")
        require(control["fixture_id"] == FIXTURES[mode], f"{control_id}: fixture/mode mismatch")
        require(control["applicability"] == "V5_REPORTS_ONLY", f"{control_id}: wrong applicability")
        require(control["expected_relation"] == EXPECTED_RELATION, f"{control_id}: wrong expected relation")
        require(isinstance(control["rationale"], str) and control["rationale"].strip(), f"{control_id}: empty rationale")

        atom_ids = control["atom_ids"]
        require(isinstance(atom_ids, list) and atom_ids, f"{control_id}: atom_ids must be nonempty")
        require(all(isinstance(atom_id, str) for atom_id in atom_ids), f"{control_id}: atom ids must be strings")
        require(len(atom_ids) == len(set(atom_ids)), f"{control_id}: duplicate atom id")
        unknown = set(atom_ids) - atom_modes.keys()
        require(not unknown, f"{control_id}: unknown atom ids {sorted(unknown)}")
        wrong_mode = [atom_id for atom_id in atom_ids if atom_modes[atom_id] != mode]
        require(not wrong_mode, f"{control_id}: atoms from another mode {wrong_mode}")

        signature = (mode, family, tuple(atom_ids))
        require(signature not in signatures, f"{control_id}: duplicate control signature")
        signatures.add(signature)
        covered_atoms.update(atom_ids)
        family_modes.add((mode, family))
        family_counts[family] += 1

    missing_family_modes = set((mode, family) for mode in MODES for family in FAMILIES) - family_modes
    require(not missing_family_modes, f"missing mode/family controls: {sorted(missing_family_modes)}")
    missing_atoms = set(atom_modes) - covered_atoms
    unknown_covered = covered_atoms - set(atom_modes)
    require(not missing_atoms, f"atoms omitted from all controls: {sorted(missing_atoms)}")
    require(not unknown_covered, f"controls contain unknown atoms: {sorted(unknown_covered)}")

    digest = hashlib.sha256(raw_controls).hexdigest()
    counts = ", ".join(f"{family}={family_counts[family]}" for family in FAMILIES)
    print(
        f"controls ok: controls={len(controls)} atoms={len(atom_modes)} "
        f"covered={len(covered_atoms)} {counts} sha256={digest}"
    )
    return digest


def main() -> None:
    validate()


if __name__ == "__main__":
    main()
