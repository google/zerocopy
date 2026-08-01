#!/usr/bin/env python3
"""Generate and verify the frozen V4 focused-evaluation artifacts."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


RUN = Path(__file__).resolve().parent
FREEZE = RUN / "freeze"
SEALED = RUN / "sealed"
EVALS = RUN.parent.parent

MODES = ("P", "B", "L", "Q", "R")
CONDITIONS = ("v4", "v3")
REPLICATES = range(1, 6)
ATOM_COUNTS = {"P": 27, "B": 15, "L": 11, "Q": 5, "R": 7}
WORD_CAPS = {"P": 3000, "B": 3200, "L": 2200, "Q": 1800, "R": 1800}

PACKAGES = {
    "v4": {
        "path": "frozen-packages/6d7e197e431b82eb81dbe7eefc79fde811e0e238435d38c69460cc068e631abb",
        "tree": "6d7e197e431b82eb81dbe7eefc79fde811e0e238435d38c69460cc068e631abb",
        "skill": "ad48b3811cf2054be76e4b461a36f63e636afb246c5dd7a75e85756a53b22d83",
    },
    "v3": {
        "path": "frozen-packages/668f70202c7bc8f23f7f894fb784a9629fd292c7f6fe69ede815b0e4c10137bf",
        "tree": "fc486dedde1f82ba232b4492808af85a12b27fa2aa27b1a35a3847b2b89f72e0",
        "skill": "0e23f7747cc63014bade7543efaf745e7e9a7e5d6dee2a48c602ef7a3eba091e",
    },
}

TARGETS = {
    "P": ("p_predicates", "2b194a735b69a8904b86baa43791a0ddac9f769ce32e87bf4e759822cb5cd52e"),
    "B": ("b_build", "7589027142112e387f990314df7eb1d08e5464448566fd68048eb2a748635bf3"),
    "L": ("l_proof", "cc05da115d055febc313edcdf18bae59a6230a63583bf918ad29e89eb06a4266"),
    "Q": ("q_quantifiers", "35bb6be0402f9d81918c3afc850dd54cde012865bba90d0cd8d7042d78a582ee"),
    "R": ("r_redesign", "d69df1b286abd8f7f8955ac56d702c1910eb596c0bd105b7998e39d7246ca063"),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def keyed(tag: str, seed: str, value: str) -> str:
    return sha256(tag.encode() + b"\0" + bytes.fromhex(seed) + b"\0" + value.encode())


def read_seeds() -> dict[str, str]:
    data = json.loads((SEALED / "seeds.json").read_text())
    expected = {
        "condition",
        "schedule",
        "blind",
        "presentation",
        "scorer",
        "consistency",
    }
    if set(data) != expected:
        raise ValueError("unexpected seed keys")
    for name, value in data.items():
        if not re.fullmatch(r"[0-9a-f]{64}", value):
            raise ValueError(f"invalid {name} seed")
        if value == "0" * 64:
            raise ValueError(f"zero {name} seed")
    if len(set(data.values())) != len(data):
        raise ValueError("randomization seeds are not distinct")
    return data


def extract_rubric(mode: str) -> str:
    source = (FREEZE / "oracle" / f"{mode}.md").read_text()
    body = source[source.index("\n") + 1 :].lstrip().rstrip() + "\n"
    atoms = re.findall(rf"^- \*\*{mode}[0-9]+\b", body, flags=re.MULTILINE)
    if len(atoms) != ATOM_COUNTS[mode]:
        raise ValueError(f"{mode}: expected {ATOM_COUNTS[mode]} atoms, found {len(atoms)}")
    if len(re.findall(r"^  - `scope_basis`:", body, flags=re.MULTILINE)) != ATOM_COUNTS[mode]:
        raise ValueError(f"{mode}: every atom must have exactly one scope_basis")
    if len(re.findall(r"^  - `dependencies`:", body, flags=re.MULTILINE)) != ATOM_COUNTS[mode]:
        raise ValueError(f"{mode}: every atom must have exactly one dependencies entry")
    return (
        f"# Mode {mode} Frozen Blind-Scoring Rubric\n\n"
        "> **Evaluator-only material. Never expose this file to a report agent.**\n\n"
        + body
    )


def generated_files(seeds: dict[str, str]) -> dict[Path, str]:
    outputs: dict[Path, str] = {}

    for mode in MODES:
        outputs[FREEZE / "rubrics" / f"{mode}.md"] = extract_rubric(mode)

    condition_order = sorted(CONDITIONS, key=lambda role: (keyed("condition-v1", seeds["condition"], role), role))
    condition_labels = {role: f"c{index}" for index, role in enumerate(condition_order)}

    mode_order = sorted(MODES, key=lambda mode: (keyed("mode-label-v1", seeds["schedule"], mode), mode))
    mode_labels = {mode: f"m{index}" for index, mode in enumerate(mode_order)}

    condition_rows = ["condition_label\trole\tpackage_path\ttree_sha256\tskill_sha256"]
    for role in condition_order:
        package = PACKAGES[role]
        condition_rows.append(
            "\t".join((condition_labels[role], role, package["path"], package["tree"], package["skill"]))
        )
    outputs[SEALED / "condition-map.tsv"] = "\n".join(condition_rows) + "\n"

    target_rows = ["target_label\tmode\tsource_path\ttree_sha256\tword_cap"]
    for mode in mode_order:
        directory, digest = TARGETS[mode]
        target_rows.append(
            f"{mode_labels[mode]}\t{mode}\tfixtures/v4-focused/{directory}\t{digest}\t{WORD_CAPS[mode]}"
        )
    outputs[SEALED / "target-map.tsv"] = "\n".join(target_rows) + "\n"

    wave_order = sorted(REPLICATES, key=lambda rep: (keyed("wave-v1", seeds["schedule"], str(rep)), rep))
    schedule_rows = ["run_id\tcell_id\twave\ttarget_label\tcondition_label\treplicate"]
    schedule: list[tuple[str, str, int, str, str, int, str, str]] = []
    run_number = 1
    for wave_index, replicate in enumerate(wave_order, start=1):
        cells = [(mode, role, replicate) for mode in MODES for role in CONDITIONS]
        cells.sort(
            key=lambda cell: (
                keyed("schedule-v1", seeds["schedule"], f"{cell[0]}|{cell[1]}|{cell[2]}"),
                cell,
            )
        )
        for mode, role, rep in cells:
            canonical = f"{mode}|{role}|{rep}"
            cell_id = keyed("cell-v1", seeds["schedule"], canonical)[:32]
            run_id = f"r{run_number:03d}"
            schedule_rows.append(
                f"{run_id}\t{cell_id}\t{wave_index}\t{mode_labels[mode]}\t{condition_labels[role]}\t{rep}"
            )
            schedule.append((run_id, cell_id, wave_index, mode, role, rep, mode_labels[mode], condition_labels[role]))
            run_number += 1
    if len(schedule) != 50 or len({row[1] for row in schedule}) != 50:
        raise ValueError("schedule does not contain 50 unique cells")
    outputs[SEALED / "launch-schedule.tsv"] = "\n".join(schedule_rows) + "\n"

    blind_rows = ["mode\tlabel\trun_id"]
    for mode in MODES:
        run_ids = [row[0] for row in schedule if row[3] == mode]
        run_ids.sort(key=lambda run_id: (keyed("blind-v1", seeds["blind"], f"{mode}|{run_id}"), run_id))
        for index, run_id in enumerate(run_ids):
            blind_rows.append(f"{mode}\t{chr(ord('A') + index)}\t{run_id}")
    outputs[SEALED / "blind-map.tsv"] = "\n".join(blind_rows) + "\n"

    presentation_rows = ["claim\tlabels_in_order"]
    for mode in MODES:
        for scorer in ("s1", "s2"):
            labels = [chr(ord("A") + index) for index in range(10)]
            labels.sort(
                key=lambda label: (
                    keyed("presentation-v1", seeds["presentation"], f"{mode}|{scorer}|{label}"),
                    label,
                )
            )
            presentation_rows.append(f"{mode}-{scorer}\t{','.join(labels)}")
    outputs[SEALED / "presentation-orders.tsv"] = "\n".join(presentation_rows) + "\n"

    claims = [f"{mode}-{scorer}" for mode in MODES for scorer in ("s1", "s2")]
    claims.sort(key=lambda claim: (keyed("scorer-v1", seeds["scorer"], claim), claim))
    outputs[SEALED / "scoring-schedule.tsv"] = "claim\n" + "\n".join(claims) + "\n"

    consistency_claims = sorted(
        MODES,
        key=lambda mode: (
            keyed("consistency-v1", seeds["consistency"], mode),
            mode,
        ),
    )
    outputs[SEALED / "consistency-schedule.tsv"] = (
        "claim\n" + "\n".join(consistency_claims) + "\n"
    )

    commitments = {
        "schema_version": 1,
        "algorithm": "sha256(tag_utf8 || NUL || seed_bytes)",
        "commitments": {
            name: sha256(f"{name}-v1".encode() + b"\0" + bytes.fromhex(seed))
            for name, seed in sorted(seeds.items())
        },
    }
    outputs[FREEZE / "randomization" / "commitments.json"] = json.dumps(commitments, indent=2, sort_keys=True) + "\n"
    return outputs


def validate_allowlists() -> None:
    for mode in MODES:
        path = FREEZE / "allowlists" / f"{mode}.txt"
        lines = path.read_text().splitlines()
        if not lines or len(lines) != len(set(lines)):
            raise ValueError(f"{mode}: empty or duplicate allowlist")
        if any(not re.fullmatch(r"https://doc\.rust-lang\.org/\S+", line) for line in lines):
            raise ValueError(f"{mode}: allowlist is not URL-only")
        source = (FREEZE / "oracle" / f"{mode}.md").read_text()
        oracle_urls = re.findall(r"https://doc\.rust-lang\.org/[^`)\s]+", source)
        if lines != oracle_urls:
            raise ValueError(f"{mode}: allowlist differs from canonical oracle URL order")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--write", action="store_true", help="write generated artifacts")
    args = parser.parse_args()

    if args.write and (FREEZE / "LOCK.json").exists():
        raise SystemExit("refusing to rewrite generated artifacts after freeze lock")

    validate_allowlists()
    outputs = generated_files(read_seeds())
    mismatches: list[str] = []
    for path, expected in outputs.items():
        if args.write:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected)
        elif not path.exists() or path.read_text() != expected:
            mismatches.append(str(path.relative_to(RUN)))
    if mismatches:
        raise SystemExit("generated artifact mismatch:\n" + "\n".join(mismatches))
    print(f"validated {len(outputs)} generated artifacts")


if __name__ == "__main__":
    main()
