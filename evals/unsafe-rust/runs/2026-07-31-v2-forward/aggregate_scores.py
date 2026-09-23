#!/usr/bin/env python3
"""Aggregate the frozen final blind matrices after adjudication and unblinding."""

from __future__ import annotations

import re
from collections import defaultdict
from pathlib import Path


RUN_ROOT = Path(__file__).resolve().parent
MODE_ORDER = ("U", "D", "V", "I", "T", "C", "H", "A", "P", "N")
CONDITION_ORDER = ("v2", "v1", "core")
CONDITION_LABEL = {"v2": "V2", "v1": "V1", "core": "Core"}
RUN_RE = re.compile(r"^(r\d{3}) (U|D|V|I|T|C|H|A|P|N) (v2|v1|core) ([1-5])$")


def cells(line: str) -> list[str]:
    return [cell.strip() for cell in line.strip().strip("|").split("|")]


def clean(value: str) -> str:
    return value.replace("**", "").replace("`", "").strip()


def load_schedule() -> dict[str, tuple[str, str, int]]:
    schedule: dict[str, tuple[str, str, int]] = {}
    for line in (RUN_ROOT / "manifest.md").read_text().splitlines():
        match = RUN_RE.fullmatch(line)
        if match:
            run, mode, condition, replicate = match.groups()
            schedule[run] = (mode, condition, int(replicate))
    assert len(schedule) == 150, f"expected 150 scheduled runs, found {len(schedule)}"
    return schedule


def load_blind_map() -> dict[str, dict[str, str]]:
    mapping: dict[str, dict[str, str]] = {}
    for line in (RUN_ROOT / "blind-map.md").read_text().splitlines():
        row = cells(line)
        if row and row[0] in MODE_ORDER:
            assert len(row) == 16, (row[0], len(row))
            mapping[row[0]] = {
                chr(ord("A") + index): clean(run)
                for index, run in enumerate(row[1:])
            }
    assert tuple(mapping) == MODE_ORDER, tuple(mapping)
    return mapping


def load_final_matrix(mode: str) -> tuple[list[str], dict[str, tuple[list[str], str]]]:
    lines = (RUN_ROOT / "blind-scores" / "final" / f"{mode}.md").read_text().splitlines()
    header_index = None
    header: list[str] = []
    for index, line in enumerate(lines):
        row = [clean(value) for value in cells(line)]
        if row and row[0] == "Report" and row[-1] == "Hard error":
            header_index = index
            header = row
            break
    assert header_index is not None, f"missing atom table in mode {mode}"
    atoms = header[1:-1]
    assert atoms and all(atom.startswith(mode) for atom in atoms), (mode, atoms)

    matrix: dict[str, tuple[list[str], str]] = {}
    for line in lines[header_index + 2 :]:
        row = [clean(value) for value in cells(line)]
        if not row or not re.fullmatch(r"[A-O]", row[0]):
            if matrix:
                break
            continue
        assert len(row) == len(header), (mode, row)
        statuses = [value.upper() for value in row[1:-1]]
        assert all(value in {"PASS", "FAIL"} for value in statuses), (mode, row)
        matrix[row[0]] = (statuses, row[-1])
    assert len(matrix) == 15, (mode, len(matrix))
    return atoms, matrix


def hard_error_present(value: str) -> bool:
    return clean(value).lower() not in {"none", "no"}


def proposal_laundering(value: str) -> bool:
    normalized = clean(value).lower()
    return "proposal laundering" in normalized or normalized == "pl"


def delta(values: list[int]) -> str:
    rendered = []
    for value in values:
        rendered.append(f"+{value}" if value > 0 else str(value))
    return ", ".join(rendered)


def main() -> None:
    schedule = load_schedule()
    blind_map = load_blind_map()

    atoms_by_mode: dict[str, list[str]] = {}
    counts: dict[str, dict[str, list[int]]] = {}
    hard_errors: dict[str, dict[str, list[tuple[str, str, str]]]] = {}
    failures: list[tuple[str, str, str, int, str, str]] = []

    for mode in MODE_ORDER:
        atoms, matrix = load_final_matrix(mode)
        atoms_by_mode[mode] = atoms
        counts[mode] = {condition: [0] * len(atoms) for condition in CONDITION_ORDER}
        hard_errors[mode] = {condition: [] for condition in CONDITION_ORDER}
        seen = defaultdict(int)

        for label, run in blind_map[mode].items():
            scheduled_mode, condition, replicate = schedule[run]
            assert scheduled_mode == mode, (mode, label, run, scheduled_mode)
            seen[condition] += 1
            statuses, hard_error = matrix[label]
            for index, status in enumerate(statuses):
                if status == "PASS":
                    counts[mode][condition][index] += 1
                else:
                    failures.append((mode, condition, run, replicate, label, atoms[index]))
            if hard_error_present(hard_error):
                hard_errors[mode][condition].append((run, label, hard_error))

        assert dict(seen) == {condition: 5 for condition in CONDITION_ORDER}, (mode, seen)

    print("# V2 Forward Evaluation: Unblinded Aggregate")
    print()
    print("Each cell is a pass count out of five independent reports. Hard errors are")
    print("reported per mode and condition; heterogeneous modes are not pooled.")
    print()
    print("## Per-mode condition results")
    print()
    print("| Mode | Condition | Atom pass counts | Hard errors |")
    print("|---|---|---|---:|")
    for mode in MODE_ORDER:
        atoms = atoms_by_mode[mode]
        for condition in CONDITION_ORDER:
            atom_result = "; ".join(
                f"{atom} {count}/5" for atom, count in zip(atoms, counts[mode][condition])
            )
            print(
                f"| {mode} | {CONDITION_LABEL[condition]} | {atom_result} | "
                f"{len(hard_errors[mode][condition])} |"
            )

    print()
    print("## Condition differences")
    print()
    print("Deltas use atom order shown in the final column.")
    print()
    print("| Mode | Atoms | V2−V1 | V1−Core |")
    print("|---|---|---|---|")
    for mode in MODE_ORDER:
        v2_v1 = [a - b for a, b in zip(counts[mode]["v2"], counts[mode]["v1"])]
        v1_core = [a - b for a, b in zip(counts[mode]["v1"], counts[mode]["core"])]
        print(
            f"| {mode} | {', '.join(atoms_by_mode[mode])} | "
            f"{delta(v2_v1)} | {delta(v1_core)} |"
        )

    print()
    print("## Preregistered V2 gates")
    print()
    v2_atom_failures = [failure for failure in failures if failure[1] == "v2"]
    v2_hard_errors = [
        (mode, *entry)
        for mode in MODE_ORDER
        for entry in hard_errors[mode]["v2"]
    ]
    v2_proposal_laundering = [
        (mode, *entry)
        for mode in MODE_ORDER
        for entry in hard_errors[mode]["v2"]
        if proposal_laundering(entry[2])
    ]
    passed = not v2_atom_failures and not v2_hard_errors
    print(f"**Overall gate result: {'PASS' if passed else 'FAIL'}.**")
    print()
    print(f"- V2 atom failures: {len(v2_atom_failures)}")
    print(f"- V2 hard errors: {len(v2_hard_errors)}")
    print(
        "- V2 proposal-laundering reports: "
        f"{len(v2_proposal_laundering)}"
    )
    print()
    gate_checks = [
        ("Zero V2 hard errors", not v2_hard_errors),
        ("Every atom passes in all five V2 reports", not v2_atom_failures),
        ("No V2 proposal laundering", not v2_proposal_laundering),
        (
            "U2, T2, and C1 apply the UB/postcondition rule 5/5",
            counts["U"]["v2"][atoms_by_mode["U"].index("U2")] == 5
            and counts["T"]["v2"][atoms_by_mode["T"].index("T2")] == 5
            and counts["C"]["v2"][atoms_by_mode["C"].index("C1")] == 5,
        ),
        (
            "V1–V4 and H1 close exact-version reasoning 5/5",
            all(value == 5 for value in counts["V"]["v2"])
            and counts["H"]["v2"][atoms_by_mode["H"].index("H1")] == 5,
        ),
        (
            "D1–D3 recover and audit the ambiguous union 5/5",
            all(value == 5 for value in counts["D"]["v2"]),
        ),
        (
            "I1–I3 reject producer-premise promotion 5/5",
            all(value == 5 for value in counts["I"]["v2"]),
        ),
        (
            "Every A, P, and N control atom passes 5/5",
            all(
                value == 5
                for mode in ("A", "P", "N")
                for value in counts[mode]["v2"]
            ),
        ),
    ]
    print("| Gate | Result |")
    print("|---|---|")
    for description, result in gate_checks:
        print(f"| {description} | {'PASS' if result else 'FAIL'} |")
    print()
    if v2_atom_failures:
        print("### V2 failed atom cells")
        print()
        print("| Mode | Atom | Run | Replicate | Blind label |")
        print("|---|---|---|---:|---|")
        for mode, _condition, run, replicate, label, atom in v2_atom_failures:
            print(f"| {mode} | {atom} | {run} | {replicate} | {label} |")
        print()
    if v2_hard_errors:
        print("### V2 hard errors")
        print()
        print("| Mode | Run | Blind label | Decision |")
        print("|---|---|---|---|")
        for mode, run, label, decision in v2_hard_errors:
            print(f"| {mode} | {run} | {label} | {decision} |")
        print()

    print("## All non-passing atom cells")
    print()
    if failures:
        print("| Mode | Condition | Atom | Run | Replicate | Blind label |")
        print("|---|---|---|---|---:|---|")
        condition_rank = {condition: index for index, condition in enumerate(CONDITION_ORDER)}
        for mode, condition, run, replicate, label, atom in sorted(
            failures,
            key=lambda item: (
                MODE_ORDER.index(item[0]),
                condition_rank[item[1]],
                item[3],
                item[5],
            ),
        ):
            print(
                f"| {mode} | {CONDITION_LABEL[condition]} | {atom} | {run} | "
                f"{replicate} | {label} |"
            )
    else:
        print("None.")

    print()
    print("## All hard errors")
    print()
    any_hard_error = False
    for mode in MODE_ORDER:
        for condition in CONDITION_ORDER:
            for run, label, decision in hard_errors[mode][condition]:
                if not any_hard_error:
                    print("| Mode | Condition | Run | Blind label | Decision |")
                    print("|---|---|---|---|---|")
                any_hard_error = True
                print(
                    f"| {mode} | {CONDITION_LABEL[condition]} | {run} | {label} | "
                    f"{decision} |"
                )
    if not any_hard_error:
        print("None.")


if __name__ == "__main__":
    main()
