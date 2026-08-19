#!/usr/bin/env python3
"""Validate closed references in the evaluator-only V5 oracle materials."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
from urllib.parse import urlsplit


FREEZE = Path(__file__).resolve().parent
MODES = ("E", "V", "F", "P", "B", "L", "R", "Q")
EXPECTED_COUNTS = {"E": 15, "V": 11, "F": 11, "P": 29, "B": 13, "L": 11, "R": 12, "Q": 13}
EXPECTED_ALLOWLIST_EXTRAS = {
    "B": {
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg",
        "https://doc.rust-lang.org/1.85.1/cargo/reference/features.html",
    }
}
EXPECTED_B_CARGO_PAGE_SHA256 = {
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#life-cycle-of-a-build-script": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#outputs-of-the-build-script": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rerun-if-env-changed": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/build-scripts.html#rustc-cfg": "1247cbaf8ce775f17349367d13ac4eecc6d9cfa343310f12d8c1deccd19e07b2",
    "https://doc.rust-lang.org/1.85.1/cargo/reference/features.html": "96b2337cd60180df5a8566f343e52938dfcaa369bf12e1e82723a2326f64cb25",
}
ATOM_KEYS = {"id", "direct_criterion", "prerequisites", "authority_dependencies", "applicability"}


def load_json(path: Path) -> object:
    try:
        text = path.read_bytes().decode("utf-8")
    except UnicodeDecodeError as error:
        raise ValueError(f"{path}: not strict UTF-8") from error

    def reject_duplicate_keys(pairs: list[tuple[str, object]]) -> dict[str, object]:
        result: dict[str, object] = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"{path}: duplicate JSON object key: {key!r}")
            result[key] = value
        return result

    def reject_nonfinite_number(token: str) -> object:
        raise ValueError(f"{path}: non-finite JSON number: {token}")

    return json.loads(
        text,
        object_pairs_hook=reject_duplicate_keys,
        parse_constant=reject_nonfinite_number,
    )


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def exact_quotations(entry: dict[str, object]) -> list[str]:
    if "quotation" in entry:
        values = [entry["quotation"]]
    else:
        values = entry.get("quotations")
    require(
        isinstance(values, list) and values and all(isinstance(value, str) and value for value in values),
        f"{entry.get('id')}: invalid exact quotation set",
    )
    return values


def records_by_id(records: object, label: str) -> dict[str, dict[str, object]]:
    require(isinstance(records, list), f"{label}: entries must be an array")
    result: dict[str, dict[str, object]] = {}
    for record in records:
        require(isinstance(record, dict), f"{label}: entry must be an object")
        record_id = record.get("id")
        require(isinstance(record_id, str) and record_id not in result, f"{label}: duplicate/invalid id {record_id!r}")
        result[record_id] = record
    return result


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

    verification_path = FREEZE / "authority" / "verification.json"
    verification = load_json(verification_path)
    require(isinstance(verification, dict), f"{verification_path}: root must be an object")
    require(
        set(verification)
        == {
            "schema_version",
            "status",
            "ready_for_freeze",
            "verification_date",
            "manifest_path",
            "rust_1_83_local_verification",
            "reused_v4_authority_binding",
            "b_cargo_corroborative_material",
            "supplied_tcb_and_dependency_evidence",
            "agent_visible_projection",
            "uncovered_authority_entries",
            "pending",
        },
        f"{verification_path}: top-level fields are not exact",
    )
    require(verification["schema_version"] == 1, "authority verification schema_version must be 1")
    require(verification["status"] == "DRAFT_VERIFIED_PENDING_CROSS_REVIEW", "authority verification must remain DRAFT")
    require(verification["ready_for_freeze"] is False, "authority verification must remain not-ready")
    require(verification["manifest_path"] == "propositions.json", "authority verification manifest path mismatch")
    require(verification["uncovered_authority_entries"] == [], "authority verification has uncovered entries")

    rust_entries = {entry_id: entry for entry_id, entry in entries.items() if entry.get("kind") == "RUST"}
    local_expected = {
        entry_id: entry for entry_id, entry in rust_entries.items() if entry.get("versions") == ["1.83.0"]
    }
    reused_expected = {entry_id: entry for entry_id, entry in rust_entries.items() if entry_id not in local_expected}
    supplied_expected = {entry_id: entry for entry_id, entry in entries.items() if entry.get("kind") != "RUST"}

    local = verification["rust_1_83_local_verification"]
    require(isinstance(local, dict) and local.get("status") == "VERIFIED", "Rust 1.83 verification record is invalid")
    require(local.get("uncovered_entries") == [], "Rust 1.83 verification has uncovered entries")
    local_records = records_by_id(local.get("entries"), "Rust 1.83 verification")
    require(set(local_records) == set(local_expected), "Rust 1.83 verification entry coverage mismatch")
    expected_page_urls: dict[str, set[str]] = {}
    for entry_id, entry in local_expected.items():
        record = local_records[entry_id]
        require(record.get("status") == "VERIFIED_LOCAL_OFFICIAL_DOCS", f"{entry_id}: wrong local verification status")
        require(record.get("quotation_count") == len(exact_quotations(entry)), f"{entry_id}: quotation-count mismatch")
        page_paths = sorted(
            {urlsplit(url).path.removeprefix("/1.83.0/") for url in entry["urls"]}
        )
        require(record.get("page_paths") == page_paths, f"{entry_id}: verified page-path mismatch")
        for url in entry["urls"]:
            path = urlsplit(url).path.removeprefix("/1.83.0/")
            expected_page_urls.setdefault(path, set()).add(url)
    local_pages = local.get("pages")
    require(isinstance(local_pages, list), "Rust 1.83 verified pages must be an array")
    pages_by_path: dict[str, dict[str, object]] = {}
    for page in local_pages:
        require(isinstance(page, dict), "Rust 1.83 verified page must be an object")
        path = page.get("path_relative_to_docs_root")
        require(isinstance(path, str) and path not in pages_by_path, f"duplicate/invalid verified page {path!r}")
        pages_by_path[path] = page
    require(set(pages_by_path) == set(expected_page_urls), "Rust 1.83 verified page coverage mismatch")
    for path, urls in expected_page_urls.items():
        require(pages_by_path[path].get("requested_urls") == sorted(urls), f"{path}: requested-URL coverage mismatch")

    reused = verification["reused_v4_authority_binding"]
    require(isinstance(reused, dict) and reused.get("status") == "BOUND_TO_FROZEN_REVIEW", "reused V4 authority binding is invalid")
    require(reused.get("uncovered_entries") == [] and reused.get("uncovered_urls") == [], "reused V4 authority has uncovered material")
    reused_records = records_by_id(reused.get("entries"), "reused V4 authority")
    require(set(reused_records) == set(reused_expected), "reused V4 authority entry coverage mismatch")
    for entry_id, entry in reused_expected.items():
        record = reused_records[entry_id]
        require(record.get("status") == "BOUND_TO_FROZEN_V4_AUTHORITY_REVIEW", f"{entry_id}: wrong reused verification status")
        require(record.get("quotation_count") == len(exact_quotations(entry)), f"{entry_id}: quotation-count mismatch")
        require(
            isinstance(record.get("requested_urls"), list)
            and sorted(record["requested_urls"]) == sorted(entry["urls"])
            and len(record["requested_urls"]) == len(set(record["requested_urls"])),
            f"{entry_id}: reused URL mismatch",
        )
    bound_pages = reused.get("bound_pages")
    require(isinstance(bound_pages, list), "reused V4 bound pages must be an array")
    bound_urls = [record.get("requested_url") for record in bound_pages if isinstance(record, dict)]
    expected_reused_urls = {url for entry in reused_expected.values() for url in entry["urls"]}
    require(set(bound_urls) == expected_reused_urls and len(bound_urls) == len(set(bound_urls)), "reused V4 bound-page coverage mismatch")

    supplied = verification["supplied_tcb_and_dependency_evidence"]
    require(isinstance(supplied, dict) and supplied.get("status") == "VERIFIED", "supplied evidence record is invalid")
    require(supplied.get("uncovered_entries") == [], "supplied evidence has uncovered entries")
    supplied_records = records_by_id(supplied.get("entries"), "supplied evidence")
    require(set(supplied_records) == set(supplied_expected), "supplied evidence entry coverage mismatch")
    repository = FREEZE.parents[4]
    for entry_id, entry in supplied_expected.items():
        record = supplied_records[entry_id]
        require(record.get("status") == "VERIFIED_EXACT_SUPPLIED_SOURCE", f"{entry_id}: wrong supplied-evidence status")
        require(record.get("quotation_count") == len(exact_quotations(entry)), f"{entry_id}: quotation-count mismatch")
        require(record.get("source_path") == entry["source_path"], f"{entry_id}: supplied source-path mismatch")
        source = repository / entry["source_path"].partition("#")[0]
        require(source.is_file(), f"{entry_id}: supplied source is absent: {source}")
        require(
            hashlib.sha256(source.read_bytes()).hexdigest() == record.get("source_sha256"),
            f"{entry_id}: supplied source digest mismatch",
        )

    projection = verification["agent_visible_projection"]
    require(isinstance(projection, dict), "agent-visible projection record is invalid")
    packet = FREEZE / "authority" / projection.get("path", "")
    require(packet.is_file(), "agent-visible projection packet is absent")
    require(hashlib.sha256(packet.read_bytes()).hexdigest() == projection.get("sha256"), "agent-visible projection digest mismatch")

    corroborative = verification.get("b_cargo_corroborative_material")
    require(isinstance(corroborative, dict), "missing B Cargo corroborative-material record")
    require(corroborative.get("status") == "BOUND_TO_FROZEN_V4_REVIEW", "wrong B Cargo provenance status")
    require(corroborative.get("atom_authority_dependency") is False, "B Cargo material must not be an atom authority dependency")
    require(corroborative.get("not_a_substitute_for") == "TCB-B-BUILD-MAP", "B Cargo material must not replace the accepted TCB entry")
    records = corroborative.get("records")
    require(isinstance(records, list) and len(records) == 5, "B Cargo corroborative record count must be five")
    observed_cargo_pages: dict[str, str] = {}
    for record in records:
        require(isinstance(record, dict), "B Cargo corroborative record must be an object")
        require(record.get("fragment_found") is True, "B Cargo corroborative fragment was not verified")
        require(isinstance(record.get("v4_review_excerpt"), str) and record["v4_review_excerpt"].strip(), "B Cargo corroborative record lacks its frozen review excerpt")
        url = record.get("requested_url")
        page_sha256 = record.get("page_sha256")
        require(isinstance(url, str) and isinstance(page_sha256, str), "B Cargo corroborative URL/hash is invalid")
        require(url not in observed_cargo_pages, f"duplicate B Cargo corroborative URL: {url}")
        observed_cargo_pages[url] = page_sha256
    require(observed_cargo_pages == EXPECTED_B_CARGO_PAGE_SHA256, "B Cargo corroborative URL/page-hash binding mismatch")
    require(set(observed_cargo_pages) == set(extras_by_mode["B"]), "B Cargo corroborative records must exactly explain B allowlist extras")

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
