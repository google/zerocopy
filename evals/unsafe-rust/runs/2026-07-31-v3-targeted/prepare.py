#!/usr/bin/env python3
"""Generate and verify the frozen V3 targeted-evaluation artifacts."""

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

MODES = ("S", "C", "X", "Q", "W", "M", "R", "K")
CONDITIONS = ("v3", "v2")
REPLICATES = range(1, 6)
ATOM_COUNTS = {"S": 7, "C": 6, "X": 13, "Q": 5, "W": 3, "M": 11, "R": 7, "K": 8}
WORD_CAPS = {"S": 1800, "C": 1800, "X": 2400, "Q": 1800, "W": 1800, "M": 1800, "R": 1800, "K": 2200}

PACKAGES = {
    "v3": {
        "path": "frozen-packages/668f70202c7bc8f23f7f894fb784a9629fd292c7f6fe69ede815b0e4c10137bf",
        "tree": "668f70202c7bc8f23f7f894fb784a9629fd292c7f6fe69ede815b0e4c10137bf",
        "skill": "0e23f7747cc63014bade7543efaf745e7e9a7e5d6dee2a48c602ef7a3eba091e",
    },
    "v2": {
        "path": "frozen-packages/40b4171cc9daf7e51ba032aef52157a85a49c4c12cea8696deadb948e0867897",
        "tree": "40b4171cc9daf7e51ba032aef52157a85a49c4c12cea8696deadb948e0867897",
        "skill": "a0a75ef8a14497aa78b50b459981097ee99605c57fec95c637cf59aaa20fe766",
    },
}

TARGETS = {
    "S": ("s_symbolic", "28ecc523e15b914a187814ab2752c0d85996948a552c62f970d8484bc6ed467a"),
    "C": ("c_conflict", "065c3cfc032af93e7576e17e49322826c4a379a707870175b16c2663d1e8e4e0"),
    "X": ("x_cross", "25b4efef689601f3b5983bf6b914bd367153d0b21a6f1f4d40de50c5d412afa7"),
    "Q": ("q_quantifiers", "c0a4c43373a159cb38d08724af8b02187b249ab6a73f7e1b10b2276f38b0cb5a"),
    "W": ("w_whole_execution", "b27b95fbc9ffa9d335bb6b4614a9f227a5798122fca79b42cf53c9b106a6aff6"),
    "M": ("m_multirelease", "b269cf068196d1c06b87be6bcded494827e7ac8a2cb6debf1eb0f0f5d0388479"),
    "R": ("r_redesign", "6d1a41909b012484d71f94d194071a7ebbb6773b7596db88127ca2a195b70ffc"),
    "K": ("k_regression", "ca272e524b36a892e25f6169631a184ff764026451eff2f6ac4ab8e9d5e87ea2"),
}

RUBRIC_RANGES = {
    "S": ("domain.md", "## S —", "## C —"),
    "C": ("domain.md", "## C —", "## X —"),
    "X": ("domain.md", "## X —", "## Exact Authority"),
    "Q": ("verdict.md", "## Q —", "## W —"),
    "W": ("verdict.md", "## W —", "## M —"),
    "M": ("verdict.md", "## M —", None),
    "R": ("controls.md", "## R —", "## K —"),
    "K": ("controls.md", "## K —", None),
}

AUTHORITY_RANGES = {
    "S": ("domain.md", "### S authorities", "### C authorities"),
    "C": ("domain.md", "### C authorities", "### X authorities"),
    "X": ("domain.md", "### X authorities", None),
    "Q": ("verdict.md", "## Q —", "## W —"),
    "W": ("verdict.md", "## W —", "## M —"),
    "M": ("verdict.md", "## M —", None),
    "R": ("controls.md", "## R —", "## K —"),
    "K": ("controls.md", "## K —", None),
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def keyed(tag: str, seed: str, value: str) -> str:
    return sha256(tag.encode() + b"\0" + bytes.fromhex(seed) + b"\0" + value.encode())


def read_seeds() -> dict[str, str]:
    data = json.loads((SEALED / "seeds.json").read_text())
    expected = {"condition", "schedule", "blind", "presentation", "scorer"}
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
    filename, start_marker, end_marker = RUBRIC_RANGES[mode]
    source = (FREEZE / "oracle" / filename).read_text()
    start = source.index(start_marker)
    end = source.index(end_marker, start + len(start_marker)) if end_marker else len(source)
    body = source[start:end].rstrip() + "\n"
    atoms = re.findall(rf"^- \*\*{mode}[0-9]+\b", body, flags=re.MULTILINE)
    if len(atoms) != ATOM_COUNTS[mode]:
        raise ValueError(f"{mode}: expected {ATOM_COUNTS[mode]} atoms, found {len(atoms)}")
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
            f"{mode_labels[mode]}\t{mode}\tfixtures/v3-targeted/{directory}\t{digest}\t{WORD_CAPS[mode]}"
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
    if len(schedule) != 80 or len({row[1] for row in schedule}) != 80:
        raise ValueError("schedule does not contain 80 unique cells")
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
        filename, start_marker, end_marker = AUTHORITY_RANGES[mode]
        source = (FREEZE / "oracle" / filename).read_text()
        start = source.index(start_marker)
        end = source.index(end_marker, start + len(start_marker)) if end_marker else len(source)
        oracle_urls = re.findall(r"https://doc\.rust-lang\.org/[^`)\s]+", source[start:end])
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
