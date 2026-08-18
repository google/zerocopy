#!/usr/bin/env python3
"""Validate closed references in the evaluator-only V5 oracle materials."""

from __future__ import annotations

import json
from pathlib import Path


FREEZE = Path(__file__).resolve().parent
MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
EXPECTED_COUNTS = {"E": 15, "V": 11, "F": 7, "P": 29, "B": 13, "L": 11, "R": 11, "Q": 12}
EXPECTED_ALLOWLIST_EXTRAS = {
    "B": {
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/features.html",
    }
}
ATOM_KEYS = {"id", "direct_criterion", "prerequisites", "authority_dependencies", "applicability"}


def load_json(path: Path) -> object:
    with path.open(encoding="utf-8") as source:
        return json.load(source)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def main() -> None:
    atom_by_id: dict[str, dict[str, object]] = {}
    atom_mode: dict[str, str] = {}

    for mode in MODES:
        path = FREEZE / "atoms" / f"{mode}.json"
        document = load_json(path)
        require(isinstance(document, dict), f"{path}: root must be an object")
        require(set(document) == {"schema_version", "status", "mode", "atoms"}, f"{path}: top-level fields are not exact")
        require(document["schema_version"] == 1 and document["status"] == "DRAFT", f"{path}: wrong schema/status")
        require(document["mode"] == mode, f"{path}: wrong mode")
        atoms = document["atoms"]
        require(isinstance(atoms, list), f"{path}: atoms must be an array")
        expected_ids = [f"{mode}{number}" for number in range(1, EXPECTED_COUNTS[mode] + 1)]
        require([atom.get("id") for atom in atoms if isinstance(atom, dict)] == expected_ids, f"{path}: atom IDs/count/order mismatch")
        for atom in atoms:
            require(isinstance(atom, dict) and set(atom) == ATOM_KEYS, f"{path}: atom fields are not exact")
            atom_id = atom["id"]
            require(atom_id not in atom_by_id, f"duplicate atom id: {atom_id}")
            require(isinstance(atom["direct_criterion"], str) and atom["direct_criterion"].strip(), f"{atom_id}: blank criterion")
            require(atom["applicability"] == "REQUIRED", f"{atom_id}: applicability must be REQUIRED")
            for field in ("prerequisites", "authority_dependencies"):
                values = atom[field]
                require(isinstance(values, list) and all(isinstance(value, str) for value in values), f"{atom_id}: invalid {field}")
                require(len(values) == len(set(values)), f"{atom_id}: duplicate {field}")
            atom_by_id[atom_id] = atom
            atom_mode[atom_id] = mode

        oracle = (FREEZE / "oracle" / f"{mode}.md").read_text(encoding="utf-8")
        require("DRAFT" in oracle and "evaluator-only" in oracle, f"oracle/{mode}.md: missing DRAFT / evaluator-only marker")

    for atom_id, atom in atom_by_id.items():
        for prerequisite in atom["prerequisites"]:
            require(prerequisite in atom_by_id, f"{atom_id}: unknown prerequisite {prerequisite}")
            require(atom_mode[prerequisite] == atom_mode[atom_id], f"{atom_id}: cross-mode prerequisite {prerequisite}")
            require(prerequisite != atom_id, f"{atom_id}: self prerequisite")

    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(atom_id: str) -> None:
        require(atom_id not in visiting, f"atom prerequisite cycle at {atom_id}")
        if atom_id in visited:
            return
        visiting.add(atom_id)
        for prerequisite in atom_by_id[atom_id]["prerequisites"]:
            visit(prerequisite)
        visiting.remove(atom_id)
        visited.add(atom_id)

    for atom_id in atom_by_id:
        visit(atom_id)

    authority_path = FREEZE / "authority" / "propositions.json"
    authority = load_json(authority_path)
    require(isinstance(authority, dict), f"{authority_path}: root must be an object")
    require(set(authority) == {"schema_version", "status", "purpose", "verification", "entries"}, f"{authority_path}: top-level fields are not exact")
    require(authority["schema_version"] == 1 and authority["status"] == "DRAFT", f"{authority_path}: wrong schema/status")
    entries: dict[str, dict[str, object]] = {}
    for entry in authority["entries"]:
        entry_id = entry.get("id")
        require(isinstance(entry_id, str) and entry_id not in entries, f"duplicate or invalid authority id: {entry_id!r}")
        urls = entry.get("urls", [])
        require(isinstance(urls, list), f"{entry_id}: urls must be an array when present")
        require(len(urls) == len(set(urls)), f"{entry_id}: duplicate urls")
        require(all(isinstance(url, str) and url.startswith("https://") for url in urls), f"{entry_id}: invalid URL")
        require(bool(urls) ^ isinstance(entry.get("source_path"), str), f"{entry_id}: needs exactly one external or supplied source form")
        require(isinstance(entry.get("consumers"), list), f"{entry_id}: consumers must be an array")
        require(len(entry["consumers"]) == len(set(entry["consumers"])), f"{entry_id}: duplicate consumers")
        require(bool(entry.get("quotation")) ^ bool(entry.get("quotations")), f"{entry_id}: needs exactly one quotation form")
        entries[entry_id] = entry

    closure_errors: list[str] = []
    for atom_id, atom in atom_by_id.items():
        for dependency in atom["authority_dependencies"]:
            if dependency not in entries:
                closure_errors.append(f"{atom_id}: unknown authority dependency {dependency}")
            elif atom_id not in entries[dependency]["consumers"]:
                closure_errors.append(f"{dependency}: missing inverse consumer {atom_id}")

    for entry_id, entry in entries.items():
        for consumer in entry["consumers"]:
            if consumer not in atom_by_id:
                closure_errors.append(f"{entry_id}: unknown consumer {consumer}")
            elif entry_id not in atom_by_id[consumer]["authority_dependencies"]:
                closure_errors.append(f"{entry_id}: stale inverse consumer {consumer}")
    require(not closure_errors, "authority/atom closure:\n" + "\n".join(closure_errors))

    extras_by_mode: dict[str, list[str]] = {}
    missing_by_mode: dict[str, list[str]] = {}
    for mode in MODES:
        allowlist_path = FREEZE / "allowlists" / f"{mode}.txt"
        urls = [line for line in allowlist_path.read_text(encoding="utf-8").splitlines() if line]
        require(len(urls) == len(set(urls)), f"{allowlist_path}: duplicate URLs")
        require(all(url.startswith("https://") for url in urls), f"{allowlist_path}: invalid URL")
        required_urls = {
            url
            for atom_id, atom in atom_by_id.items()
            if atom_mode[atom_id] == mode
            for dependency in atom["authority_dependencies"]
            for url in entries[dependency].get("urls", [])
        }
        missing = required_urls - set(urls)
        missing_by_mode[mode] = sorted(missing)
        extras_by_mode[mode] = sorted(set(urls) - required_urls)
        require(
            set(extras_by_mode[mode]) == EXPECTED_ALLOWLIST_EXTRAS.get(mode, set()),
            f"{allowlist_path}: unexpected allowlist extras {extras_by_mode[mode]}",
        )

    require(
        not any(missing_by_mode.values()),
        "allowlist closure:\n"
        + "\n".join(f"{mode}: {urls}" for mode, urls in missing_by_mode.items() if urls),
    )

    print(
        "oracle materials ok: "
        f"atoms={len(atom_by_id)} authority_entries={len(entries)} "
        f"allowlist_extras={sum(len(urls) for urls in extras_by_mode.values())}"
    )
    for mode in MODES:
        if extras_by_mode[mode]:
            print(f"allowlist extras {mode}: {extras_by_mode[mode]}")


if __name__ == "__main__":
    main()
