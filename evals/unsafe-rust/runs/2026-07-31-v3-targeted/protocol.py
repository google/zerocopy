#!/usr/bin/env python3
"""Frozen mechanics for the V3 targeted evaluation.

This program validates immutable inputs, prepares neutral report cells, builds
blind packets, reconciles dual scores, and aggregates only after adjudication.
It never runs or builds a target.
"""

from __future__ import annotations

import argparse
import csv
import fcntl
import hashlib
import json
import os
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import io
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import prepare


RUN = Path(__file__).resolve().parent
FREEZE = RUN / "freeze"
SEALED = RUN / "sealed"
COLLECTION = RUN / "collection"
SCORING = RUN / "scoring"
RESULTS = RUN / "results"
EVALS = RUN.parent.parent
MODES = prepare.MODES
LABELS = tuple(chr(ord("A") + index) for index in range(10))
SCORERS = ("s1", "s2")
GLOBAL_HARD_ERROR_COUNT = 12
INFRA_FAILURE_CODES = {
    "SERVICE_ERROR_BEFORE_OUTPUT",
    "ORCHESTRATOR_TOOL_FAILURE",
    "FILESYSTEM_FAILURE",
}
TERMINAL_REPORT_FAILURE_CODES = {
    "REFUSAL",
    "TIMEOUT_AFTER_WORK",
    "INVALID_OUTPUT",
    "SEMANTIC_NONCOMPLETION",
}
FILE_MANIFEST = FREEZE / "file-manifest.sha256"
LOCK = FREEZE / "LOCK.json"
OPERATION_LOCK = RUN / "operations.lock"
EVENT_PHASES = {"freeze", "collection", "scoring", "adjudication", "unblinding", "result"}
_AUTHENTICATED_FILE_DIGESTS: dict[str, str] | None = None


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def positive_int(value: str) -> int:
    parsed = int(value)
    if parsed < 1:
        raise argparse.ArgumentTypeError("value must be a positive integer")
    return parsed


def acquire_operation_lock() -> Any:
    OPERATION_LOCK.parent.mkdir(parents=True, exist_ok=True)
    handle = OPERATION_LOCK.open("a+", encoding="utf-8")
    fcntl.flock(handle, fcntl.LOCK_EX)
    return handle


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    return sha256_bytes(path.read_bytes())


def json_dump(value: Any) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def is_nonblank_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def read_tsv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as file:
        return list(csv.DictReader(file, dialect="excel-tab"))


def read_frozen_tsv(path: Path) -> list[dict[str, str]]:
    data = read_frozen_bytes(path)
    return list(csv.DictReader(io.StringIO(data.decode()), dialect="excel-tab"))


def read_frozen_bytes(path: Path) -> bytes:
    data = path.read_bytes()
    if FILE_MANIFEST.exists() and sha256_bytes(data) != frozen_file_digest(path):
        raise ValueError(f"frozen input changed while being read: {path.relative_to(RUN)}")
    return data


def read_frozen_text(path: Path) -> str:
    return read_frozen_bytes(path).decode()


def write_once(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("x", encoding="utf-8", newline="") as file:
        file.write(content)
        file.flush()
        os.fsync(file.fileno())


def write_bytes_once(path: Path, content: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as file:
        file.write(content)
        file.flush()
        os.fsync(file.fileno())


def load_schedule() -> dict[str, dict[str, str]]:
    rows = read_frozen_tsv(SEALED / "launch-schedule.tsv")
    return {row["run_id"]: row for row in rows}


def load_condition_map() -> dict[str, dict[str, str]]:
    return {
        row["condition_label"]: row
        for row in read_frozen_tsv(SEALED / "condition-map.tsv")
    }


def load_target_map() -> dict[str, dict[str, str]]:
    return {
        row["target_label"]: row for row in read_frozen_tsv(SEALED / "target-map.tsv")
    }


def load_blind_map() -> dict[str, dict[str, str]]:
    by_mode: dict[str, dict[str, str]] = {mode: {} for mode in MODES}
    for row in read_frozen_tsv(SEALED / "blind-map.tsv"):
        by_mode[row["mode"]][row["label"]] = row["run_id"]
    return by_mode


def load_frozen_seeds() -> dict[str, str]:
    data = json.loads(read_frozen_text(SEALED / "seeds.json"))
    expected = {"condition", "schedule", "blind", "presentation", "scorer"}
    if not isinstance(data, dict) or set(data) != expected:
        raise ValueError("unexpected frozen seed keys")
    if any(
        not isinstance(value, str)
        or not re.fullmatch(r"[0-9a-f]{64}", value)
        or value == "0" * 64
        for value in data.values()
    ):
        raise ValueError("invalid frozen randomization seed")
    if len(set(data.values())) != len(data):
        raise ValueError("frozen randomization seeds are not distinct")
    return data


def mode_for_run(run_id: str) -> str:
    row = load_schedule()[run_id]
    return load_target_map()[row["target_label"]]["mode"]


def atom_ids(mode: str) -> tuple[str, ...]:
    text = read_frozen_text(FREEZE / "rubrics" / f"{mode}.md")
    atoms = tuple(re.findall(rf"^- \*\*({mode}[1-9][0-9]*)\b", text, flags=re.MULTILINE))
    if len(atoms) != prepare.ATOM_COUNTS[mode] or len(set(atoms)) != len(atoms):
        raise ValueError(f"invalid atom inventory for mode {mode}: {atoms}")
    return atoms


def mode_hard_error_ids(mode: str) -> tuple[str, ...]:
    text = read_frozen_text(FREEZE / "rubrics" / f"{mode}.md")
    match = re.search(
        r"^#{2,6}[^\n]*hard[^\n]*\n(.*?)(?=^#{1,6} |\Z)",
        text,
        flags=re.MULTILINE | re.DOTALL | re.IGNORECASE,
    )
    if not match:
        raise ValueError(f"missing hard-error section for mode {mode}")
    body = match.group(1)
    count = len(re.findall(r"^- ", body, flags=re.MULTILINE))
    if not count:
        raise ValueError(f"empty hard-error section for mode {mode}")
    return tuple(f"{mode}H{index}" for index in range(1, count + 1))


def hard_error_ids(mode: str) -> tuple[str, ...]:
    return tuple(f"G{index}" for index in range(1, GLOBAL_HARD_ERROR_COUNT + 1)) + mode_hard_error_ids(mode)


def tar_tree_digest(path: Path) -> str:
    if path.is_symlink() or not path.is_dir():
        raise ValueError(f"not a directory: {path}")
    if any(item.is_symlink() for item in path.rglob("*")):
        raise ValueError(f"symlink prohibited in frozen tree: {path}")
    command = [
        "tar",
        "--sort=name",
        "--mtime=@0",
        "--owner=0",
        "--group=0",
        "--numeric-owner",
        "-C",
        str(path),
        "-cf",
        "-",
        ".",
    ]
    completed = subprocess.run(command, check=True, stdout=subprocess.PIPE)
    return sha256_bytes(completed.stdout)


def byte_tree_digest(path: Path) -> str:
    if path.is_symlink() or not path.is_dir():
        raise ValueError(f"byte-tree root is not a real directory: {path}")
    records: list[bytes] = []
    for item in sorted(path.rglob("*"), key=lambda value: value.relative_to(path).as_posix()):
        relative = item.relative_to(path).as_posix()
        if item.is_symlink() or not (item.is_dir() or item.is_file()):
            raise ValueError(f"unsupported runtime entry: {item}")
        if item.is_dir():
            records.append(f"d\0{relative}\n".encode())
        else:
            data = item.read_bytes()
            records.append(
                f"f\0{relative}\0{len(data)}\0{sha256_bytes(data)}\n".encode()
            )
    return sha256_bytes(b"".join(records))


def lock_input_paths() -> list[Path]:
    paths: list[Path] = []
    for name in ("prepare.py", "fetch_authority.py", "protocol.py"):
        paths.append(RUN / name)
    for root in (FREEZE, SEALED):
        for path in root.rglob("*"):
            if not path.is_file():
                continue
            if path in {FILE_MANIFEST, LOCK} or "__pycache__" in path.parts:
                continue
            paths.append(path)
    paths.sort(key=lambda path: path.relative_to(RUN).as_posix())
    if any(path.is_symlink() for path in paths):
        raise ValueError("symlinks are prohibited in lock inputs")
    return paths


def render_file_manifest() -> str:
    return "".join(
        f"{sha256_file(path)}  {path.relative_to(RUN).as_posix()}\n"
        for path in lock_input_paths()
    )


def verify_file_manifest() -> None:
    if not FILE_MANIFEST.exists():
        raise ValueError("missing file-manifest.sha256")
    expected = render_file_manifest()
    actual = FILE_MANIFEST.read_text()
    if actual != expected:
        raise ValueError("freeze file manifest does not match current inputs")


def parse_file_manifest(data: bytes) -> dict[str, str]:
    entries: dict[str, str] = {}
    for line in data.decode().splitlines():
        digest, separator, name = line.partition("  ")
        if (
            not separator
            or not name
            or name in entries
            or not re.fullmatch(r"[0-9a-f]{64}", digest)
        ):
            raise ValueError("invalid frozen file-manifest row")
        entries[name] = digest
    return entries


def frozen_file_digest(path: Path) -> str:
    relative = path.relative_to(RUN).as_posix()
    if _AUTHENTICATED_FILE_DIGESTS is not None:
        entries = _AUTHENTICATED_FILE_DIGESTS
    else:
        data = FILE_MANIFEST.read_bytes()
        if LOCK.exists():
            lock = json.loads(LOCK.read_text())
            if lock.get("file_manifest_sha256") != sha256_bytes(data):
                raise ValueError("file manifest is not authenticated by LOCK.json")
        entries = parse_file_manifest(data)
    if relative not in entries:
        raise ValueError(f"path is not pinned by the freeze manifest: {relative}")
    return entries[relative]


def validate_static(require_lock: bool, *, announce: bool = True) -> None:
    global _AUTHENTICATED_FILE_DIGESTS
    prepare.validate_allowlists()
    generated = prepare.generated_files(prepare.read_seeds())
    for path, expected in generated.items():
        if not path.exists() or read_frozen_text(path) != expected:
            raise ValueError(f"generated artifact mismatch: {path.relative_to(RUN)}")

    for role, package in prepare.PACKAGES.items():
        path = EVALS / package["path"]
        actual = tar_tree_digest(path)
        if actual != package["tree"]:
            raise ValueError(f"{role} package digest mismatch: {actual}")
        skill = sha256_file(path / "SKILL.md")
        if skill != package["skill"]:
            raise ValueError(f"{role} SKILL.md digest mismatch: {skill}")
    for mode, (directory, expected) in prepare.TARGETS.items():
        actual = tar_tree_digest(EVALS / "fixtures" / "v3-targeted" / directory)
        if actual != expected:
            raise ValueError(f"{mode} target digest mismatch: {actual}")

    schedule_rows = read_frozen_tsv(SEALED / "launch-schedule.tsv")
    if len(schedule_rows) != 80:
        raise ValueError(f"expected 80 schedule rows, found {len(schedule_rows)}")
    if len({row["run_id"] for row in schedule_rows}) != 80:
        raise ValueError("duplicate run ID")
    if len({row["cell_id"] for row in schedule_rows}) != 80:
        raise ValueError("duplicate cell ID")
    target_map = load_target_map()
    condition_map = load_condition_map()
    wave_counts: Counter[tuple[str, str, str]] = Counter()
    for row in schedule_rows:
        mode = target_map[row["target_label"]]["mode"]
        role = condition_map[row["condition_label"]]["role"]
        wave_counts[(row["wave"], mode, role)] += 1
    expected_wave_counts = Counter(
        (str(wave), mode, role)
        for wave in range(1, 6)
        for mode in MODES
        for role in prepare.CONDITIONS
    )
    if wave_counts != expected_wave_counts:
        raise ValueError("schedule is not five complete balanced waves")

    blind = load_blind_map()
    mapped_runs: list[str] = []
    for mode in MODES:
        if tuple(sorted(blind[mode])) != LABELS:
            raise ValueError(f"{mode} blind labels are incomplete")
        for run_id in blind[mode].values():
            if mode_for_run(run_id) != mode:
                raise ValueError(f"blind map crosses modes: {mode} {run_id}")
            mapped_runs.append(run_id)
        atom_ids(mode)
        mode_hard_error_ids(mode)
    if Counter(mapped_runs) != Counter(row["run_id"] for row in schedule_rows):
        raise ValueError("blind map is not a bijection over scheduled runs")

    presentations = read_frozen_tsv(SEALED / "presentation-orders.tsv")
    if {row["claim"] for row in presentations} != {
        f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS
    }:
        raise ValueError("presentation claims are incomplete")
    for row in presentations:
        if tuple(sorted(row["labels_in_order"].split(","))) != LABELS:
            raise ValueError(f"invalid presentation order: {row['claim']}")

    for schema in (FREEZE / "schemas").glob("*.json"):
        json.loads(read_frozen_text(schema))

    authority = FREEZE / "authority-manifest.tsv"
    if not authority.exists():
        raise ValueError("missing authority-manifest.tsv")
    authority_rows = read_frozen_tsv(authority)
    allowlist_pairs = [
        (mode, url)
        for mode in MODES
        for url in read_frozen_text(FREEZE / "allowlists" / f"{mode}.txt").splitlines()
    ]
    if [(row["mode"], row["requested_url"]) for row in authority_rows] != allowlist_pairs:
        raise ValueError("authority manifest does not match exact allowlist sequence")
    if any(
        row["status"] != "200"
        or row["fragment_found"] != "true"
        or not re.fullmatch(r"[0-9a-f]{64}", row["sha256"])
        for row in authority_rows
    ):
        raise ValueError("authority manifest has an invalid retrieval record")
    validate_event_ledger()
    validate_preserved_artifacts()

    if require_lock:
        verify_file_manifest()
        lock = json.loads(LOCK.read_text())
        if set(lock) != {
            "schema_version",
            "status",
            "file_manifest_sha256",
            "review_signoffs",
            "reports_collected_before_lock",
            "locked_utc",
        }:
            raise ValueError("freeze lock has unexpected fields")
        if type(lock.get("schema_version")) is not int or lock["schema_version"] != 1 or lock.get("status") != "FROZEN":
            raise ValueError("invalid freeze lock")
        locked_utc = lock.get("locked_utc")
        if not isinstance(locked_utc, str):
            raise ValueError("invalid freeze lock timestamp")
        try:
            locked_time = datetime.fromisoformat(locked_utc.replace("Z", "+00:00"))
        except ValueError as error:
            raise ValueError("invalid freeze lock timestamp") from error
        if locked_time.tzinfo is None:
            raise ValueError("freeze lock timestamp lacks timezone")
        root = sha256_file(FILE_MANIFEST)
        if lock.get("file_manifest_sha256") != root:
            raise ValueError("freeze lock root does not match file manifest")
        signoffs = lock.get("review_signoffs", [])
        if not isinstance(signoffs, list) or len(signoffs) < 2 or any(
            not isinstance(signoff, dict) for signoff in signoffs
        ):
            raise ValueError("freeze lock lacks two review signoffs")
        reviewer_ids = [signoff.get("reviewer_id") for signoff in signoffs]
        if any(
            not isinstance(reviewer_id, str)
            or not reviewer_id
            or reviewer_id != reviewer_id.strip()
            for reviewer_id in reviewer_ids
        ):
            raise ValueError("freeze lock has an empty reviewer ID")
        if len(set(reviewer_ids)) != len(signoffs):
            raise ValueError("freeze lock reviewer IDs are not distinct")
        for signoff in signoffs:
            if set(signoff) != {
                "reviewer_id",
                "verdict",
                "file_manifest_sha256",
                "scope",
                "reviewed_utc",
            }:
                raise ValueError("freeze review signoff has unexpected fields")
            scope = signoff.get("scope")
            reviewed_utc = signoff.get("reviewed_utc")
            if (
                signoff.get("verdict") != "PASS/FREEZE"
                or signoff.get("file_manifest_sha256") != root
                or not isinstance(scope, str)
                or not scope.strip()
                or scope != scope.strip()
                or not isinstance(reviewed_utc, str)
                or not reviewed_utc.strip()
                or reviewed_utc != reviewed_utc.strip()
            ):
                raise ValueError("invalid freeze review signoff")
            try:
                reviewed_time = datetime.fromisoformat(reviewed_utc.replace("Z", "+00:00"))
            except ValueError as error:
                raise ValueError("invalid freeze review timestamp") from error
            if reviewed_time.tzinfo is None:
                raise ValueError("freeze review timestamp lacks timezone")
        if (
            type(lock.get("reports_collected_before_lock")) is not int
            or lock["reports_collected_before_lock"] != 0
        ):
            raise ValueError("freeze lock does not attest zero prior reports")
        freeze_events = [event for event in event_records() if event["event"] == "freeze_locked"]
        if len(freeze_events) > 1:
            raise ValueError("multiple freeze-lock events")
        if freeze_events:
            freeze_sequence = freeze_events[0]["sequence"]
            if any(
                event["sequence"] < freeze_sequence and event["phase"] != "freeze"
                for event in event_records()
            ):
                raise ValueError("evaluation activity predates the freeze-lock event")
        elif any(
            path.is_file()
            for root in (COLLECTION, SCORING, RESULTS)
            if root.exists()
            for path in root.rglob("*")
        ):
            raise ValueError("evaluation artifacts exist before the freeze-lock event")
        _AUTHENTICATED_FILE_DIGESTS = parse_file_manifest(FILE_MANIFEST.read_bytes())
        if "**Preregistration status:** FROZEN." not in read_frozen_text(
            FREEZE / "plan.md"
        ):
            raise ValueError("plan is not marked FROZEN")
    if announce:
        print("static protocol validation passed")


def make_read_only(path: Path) -> None:
    for item in sorted(path.rglob("*"), reverse=True):
        if item.is_file():
            os.utime(item, (0, 0), follow_symlinks=False)
            item.chmod(0o444)
        elif item.is_dir():
            os.utime(item, (0, 0), follow_symlinks=False)
            item.chmod(0o555)
    os.utime(path, (0, 0), follow_symlinks=False)
    path.chmod(0o555)


def resolve_run(run_id: str) -> tuple[dict[str, str], dict[str, str], dict[str, str]]:
    schedule = load_schedule()
    if run_id not in schedule:
        raise ValueError(f"unknown run ID: {run_id}")
    row = schedule[run_id]
    target = load_target_map()[row["target_label"]]
    condition = load_condition_map()[row["condition_label"]]
    return row, target, condition


def event_records() -> list[dict[str, Any]]:
    path = RUN / "events.jsonl"
    return [json.loads(line) for line in path.read_text().splitlines()] if path.exists() else []


def assert_authority_verification_allowed(wave: int) -> None:
    if wave not in range(1, 6):
        raise ValueError(f"invalid collection wave: {wave}")
    events = event_records()
    if any(
        event["event"] == "authority_verified"
        and event.get("details", {}).get("wave") == wave
        for event in events
    ):
        raise ValueError(f"wave {wave} authority verification was already recorded")
    schedule_rows = read_frozen_tsv(SEALED / "launch-schedule.tsv")
    completed = {event.get("run_id") for event in events if event["event"] == "report_preserved"}
    required_completed = {
        row["run_id"] for row in schedule_rows if int(row["wave"]) < wave
    }
    if not required_completed <= completed:
        raise ValueError(f"earlier collection waves are incomplete before wave {wave}")
    prepared = {event.get("run_id") for event in events if event["event"] == "cell_prepared"}
    current = {row["run_id"] for row in schedule_rows if int(row["wave"]) == wave}
    if prepared & current:
        raise ValueError(f"wave {wave} authority verification must precede cell preparation")


def assert_prepare_allowed(run_id: str) -> None:
    schedule_rows = read_frozen_tsv(SEALED / "launch-schedule.tsv")
    order = [row["run_id"] for row in schedule_rows]
    position = order.index(run_id)
    row = schedule_rows[position]
    events = event_records()
    authority_events = [
        event
        for event in events
        if event["event"] == "authority_verified"
        and event.get("details", {}).get("wave") == int(row["wave"])
        and event.get("sha256") == sha256_file(FREEZE / "authority-manifest.tsv")
    ]
    if len(authority_events) != 1:
        raise ValueError(f"wave {row['wave']} lacks one current authority verification")
    prepared = {event.get("run_id") for event in events if event["event"] == "cell_prepared"}
    completed = {event.get("run_id") for event in events if event["event"] == "report_preserved"}
    if run_id in prepared:
        raise ValueError(f"cell already prepared: {run_id}")
    earlier_in_wave = {
        prior["run_id"]
        for prior in schedule_rows[:position]
        if prior["wave"] == row["wave"]
    }
    if not earlier_in_wave <= prepared:
        raise ValueError(f"prepare order violation before {run_id}")
    earlier_waves = {
        prior["run_id"] for prior in schedule_rows if int(prior["wave"]) < int(row["wave"])
    }
    if not earlier_waves <= completed:
        raise ValueError(f"wave barrier violation before {run_id}")
    if len(prepared - completed) >= 3:
        raise ValueError(f"three report cells are already active before {run_id}")


def record_agent_start(run_id: str, attempt: int, agent_id: str) -> None:
    if attempt < 1:
        raise ValueError("report attempt must be positive")
    if not agent_id:
        raise ValueError("agent ID must be nonempty")
    events = event_records()
    if not any(event["event"] == "cell_prepared" and event.get("run_id") == run_id for event in events):
        raise ValueError(f"cell was not prepared: {run_id}")
    key = (run_id, attempt)
    started = {
        (event.get("run_id"), event.get("attempt"))
        for event in events
        if event["event"] == "agent_started"
    }
    returned = {
        (event.get("run_id"), event.get("attempt"))
        for event in events
        if event["event"] == "agent_returned"
    }
    if key in started:
        raise ValueError(f"agent attempt already started: {run_id}/{attempt}")
    used_agent_ids = {
        event.get("agent_id")
        for event in events
        if event["event"] in {"agent_started", "evaluator_started"}
    }
    if agent_id in used_agent_ids:
        raise ValueError(f"agent ID was already used by an evaluated agent: {agent_id}")
    if len(started - returned) >= 3:
        raise ValueError("three report agents are already active")
    schedule_rows = read_frozen_tsv(SEALED / "launch-schedule.tsv")
    position = next(index for index, row in enumerate(schedule_rows) if row["run_id"] == run_id)
    current_wave = schedule_rows[position]["wave"]
    earlier_in_wave = [
        row["run_id"] for row in schedule_rows[:position] if row["wave"] == current_wave
    ]
    started_runs = {item[0] for item in started}
    if not all(prior in started_runs for prior in earlier_in_wave):
        raise ValueError(f"agent launch-order violation before {run_id}")
    if attempt > 1 and not any(
        event["event"] == "infrastructure_failure"
        and event.get("run_id") == run_id
        and event.get("attempt") == attempt - 1
        for event in events
    ):
        raise ValueError("fresh attempt lacks a preceding infrastructure failure")
    setup = json.loads((COLLECTION / "setups" / f"{run_id}.json").read_text())
    runtime = Path(setup["runtime_root"])
    verify_runtime(run_id, runtime)
    prompt_digest = sha256_bytes(render_report_prompt(run_id, runtime).encode())
    if setup.get("report_prompt_sha256") != prompt_digest:
        raise ValueError(f"rendered report prompt changed for {run_id}")
    output_entries_now = list((runtime / "output").iterdir())
    if output_entries_now:
        raise ValueError(f"report output is not initially empty: {run_id}/{attempt}")
    append_event(
        "collection",
        "agent_started",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        details={
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
            "fork_turns": "none",
            "prompt_sha256": prompt_digest,
        },
    )


def record_prelaunch_failure(run_id: str, evidence: str) -> None:
    if not evidence.strip():
        raise ValueError("prelaunch failure requires nonempty evidence")
    resolve_run(run_id)
    events = event_records()
    if not any(
        event["event"] == "cell_prepared" and event.get("run_id") == run_id
        for event in events
    ):
        raise ValueError(f"cell was not prepared: {run_id}")
    started = [
        event
        for event in events
        if event["event"] == "agent_started" and event.get("run_id") == run_id
    ]
    returned_attempts = {
        event.get("attempt")
        for event in events
        if event["event"] == "agent_returned" and event.get("run_id") == run_id
    }
    if any(event["attempt"] not in returned_attempts for event in started):
        raise ValueError("cannot record a prelaunch failure while a report agent is active")
    if any(
        event["event"] == "report_preserved" and event.get("run_id") == run_id
        for event in events
    ):
        raise ValueError("cannot record a prelaunch failure after canonical completion")
    next_attempt = max((event["attempt"] for event in started), default=0) + 1
    append_event(
        "collection",
        "prelaunch_failure",
        run_id=run_id,
        details={
            "disposition": "API_NO_AGENT_START",
            "next_attempt": next_attempt,
            "evidence": evidence,
        },
    )


def assert_agent_started(run_id: str, attempt: int, agent_id: str) -> None:
    matches = [
        event
        for event in event_records()
        if event["event"] == "agent_started"
        and event.get("run_id") == run_id
        and event.get("attempt") == attempt
        and event.get("agent_id") == agent_id
    ]
    if len(matches) != 1:
        raise ValueError(f"missing unique agent-start record: {run_id}/{attempt}/{agent_id}")


def record_reminder(run_id: str, attempt: int, agent_id: str) -> None:
    assert_agent_started(run_id, attempt, agent_id)
    events = event_records()
    if any(
        event["event"] == "reminder_sent"
        and event.get("run_id") == run_id
        and event.get("attempt") == attempt
        for event in events
    ):
        raise ValueError("the one permitted reminder was already recorded")
    if any(
        event["event"] == "agent_returned"
        and event.get("run_id") == run_id
        and event.get("attempt") == attempt
        for event in events
    ):
        raise ValueError("a reminder cannot follow agent return")
    start = next(
        event
        for event in events
        if event["event"] == "agent_started"
        and event.get("run_id") == run_id
        and event.get("attempt") == attempt
    )
    started = datetime.fromisoformat(start["time_utc"].replace("Z", "+00:00"))
    if (datetime.now(timezone.utc) - started).total_seconds() < 180:
        raise ValueError("reminder is not permitted before 180 seconds")
    append_event(
        "collection",
        "reminder_sent",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        details={"text_sha256": sha256_bytes(report_reminder_text().encode())},
    )


def assert_evaluator_attempt_allowed(
    kind: str, identity: str, attempt: int, events: list[dict[str, Any]] | None = None
) -> None:
    if kind not in {"scorer", "adjudicator"} or attempt < 1:
        raise ValueError(f"invalid evaluator attempt: {kind}/{identity}/{attempt}")
    events = event_records() if events is None else events
    if any(
        event["event"] == "evaluator_started"
        and event.get("attempt") == attempt
        and event.get("details", {}).get("kind") == kind
        and event.get("details", {}).get("identity") == identity
        for event in events
    ):
        raise ValueError(f"evaluator attempt already started: {kind}/{identity}/{attempt}")
    completion_event = "score_preserved" if kind == "scorer" else "adjudication_preserved"
    if any(
        event["event"] == completion_event
        and (
            (kind == "scorer" and f"{event.get('details', {}).get('mode')}-{event.get('details', {}).get('scorer')}" == identity)
            or (kind == "adjudicator" and event.get("details", {}).get("mode") == identity)
        )
        for event in events
    ):
        raise ValueError(f"evaluator identity already completed: {kind}/{identity}")
    if attempt > 1 and not any(
        event["event"] == "evaluator_infrastructure_failure"
        and event.get("attempt") == attempt - 1
        and event.get("details", {}).get("kind") == kind
        and event.get("details", {}).get("identity") == identity
        for event in events
    ):
        raise ValueError("fresh evaluator retry lacks a preceding infrastructure failure")


def record_evaluator_start(kind: str, identity: str, attempt: int, agent_id: str) -> None:
    if kind not in {"scorer", "adjudicator"}:
        raise ValueError(f"unknown evaluator kind: {kind}")
    events = event_records()
    assert_evaluator_attempt_allowed(kind, identity, attempt, events)
    key = (kind, identity, attempt)
    started = {
        (
            event.get("details", {}).get("kind"),
            event.get("details", {}).get("identity"),
            event.get("attempt"),
        )
        for event in events
        if event["event"] == "evaluator_started"
    }
    returned = {
        (
            event.get("details", {}).get("kind"),
            event.get("details", {}).get("identity"),
            event.get("attempt"),
        )
        for event in events
        if event["event"] == "evaluator_returned"
    }
    used_agent_ids = {
        event.get("agent_id")
        for event in events
        if event["event"] in {"agent_started", "evaluator_started"}
    }
    if agent_id in used_agent_ids:
        raise ValueError(f"agent ID was already used by an evaluated agent: {agent_id}")
    if len(started - returned) >= 3:
        raise ValueError("three evaluator agents are already active")
    if kind == "scorer":
        claims = [row["claim"] for row in read_frozen_tsv(SEALED / "scoring-schedule.tsv")]
        if identity not in claims:
            raise ValueError(f"unknown scorer claim: {identity}")
        prior = claims[: claims.index(identity)]
        started_identities = {(item[0], item[1]) for item in started}
        if not all(("scorer", claim) in started_identities for claim in prior):
            raise ValueError(f"scorer launch-order violation before {identity}")
        mode, scorer = identity.split("-", 1)
        source_packet = SCORING / "packets" / mode / scorer
        verify_score_packet(mode, scorer)
    else:
        source_packet = SCORING / "adjudication-packets" / identity
        if not source_packet.exists():
            raise ValueError(f"adjudication packet does not exist: {identity}")
        verify_adjudication_packet(identity)
    output = expected_evaluator_output(kind, identity, attempt)
    verify_evaluator_runtime(kind, identity, attempt, source_packet, output)
    if output.is_symlink() or not output.is_dir() or any(output.iterdir()):
        raise ValueError(f"evaluator output is not initially empty: {kind}/{identity}")
    append_event(
        "scoring" if kind == "scorer" else "adjudication",
        "evaluator_started",
        attempt=attempt,
        agent_id=agent_id,
        details={
            "kind": kind,
            "identity": identity,
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
            "fork_turns": "none",
            "prompt_sha256": sha256_bytes(
                render_packet_prompt(
                    "scorer.md" if kind == "scorer" else "adjudicator.md",
                    expected_evaluator_packet(kind, identity, attempt),
                    output,
                    **({"SCORER_ID": identity.split("-", 1)[1]} if kind == "scorer" else {}),
                ).encode()
            ),
        },
    )


def assert_evaluator_started(
    kind: str, identity: str, attempt: int, agent_id: str
) -> None:
    matches = [
        event
        for event in event_records()
        if event["event"] == "evaluator_started"
        and event.get("attempt") == attempt
        and event.get("agent_id") == agent_id
        and event.get("details", {}).get("kind") == kind
        and event.get("details", {}).get("identity") == identity
    ]
    if len(matches) != 1:
        raise ValueError(
            f"missing evaluator-start record: {kind}/{identity}/{attempt}/{agent_id}"
        )


def record_evaluator_prelaunch_failure(
    kind: str, identity: str, attempt: int, output: Path, evidence: str
) -> None:
    if not evidence.strip():
        raise ValueError("evaluator prelaunch failure requires nonempty evidence")
    assert_evaluator_attempt_allowed(kind, identity, attempt)
    if kind == "scorer":
        mode, scorer = identity.split("-", 1)
        source_packet = SCORING / "packets" / mode / scorer
        verify_score_packet(mode, scorer)
    else:
        source_packet = SCORING / "adjudication-packets" / identity
        verify_adjudication_packet(identity)
    verify_evaluator_runtime(kind, identity, attempt, source_packet, output)
    if any(output.iterdir()):
        raise ValueError("prelaunch evaluator output is not empty")
    append_event(
        "scoring" if kind == "scorer" else "adjudication",
        "evaluator_prelaunch_failure",
        attempt=attempt,
        details={
            "kind": kind,
            "identity": identity,
            "disposition": "API_NO_AGENT_START",
            "evidence": evidence,
        },
    )


def prepare_cell(run_id: str, runtime: Path) -> None:
    validate_static(require_lock=True, announce=False)
    assert_prepare_allowed(run_id)
    if runtime.exists():
        raise FileExistsError(f"runtime already exists: {runtime}")
    row, target, condition = resolve_run(run_id)
    expected_runtime = Path("/tmp/ur-eval") / row["cell_id"]
    if runtime != expected_runtime:
        raise ValueError(f"runtime must be the frozen neutral path {expected_runtime}")
    package_source = EVALS / condition["package_path"]
    target_source = EVALS / target["source_path"]
    runtime.mkdir(parents=True)
    shutil.copytree(package_source, runtime / "package")
    shutil.copytree(target_source, runtime / "target")
    shutil.copy2(FREEZE / "allowlists" / f"{target['mode']}.txt", runtime / "allowlist.txt")
    (runtime / "output").mkdir()
    if tar_tree_digest(runtime / "package") != condition["tree_sha256"]:
        raise ValueError(f"package runtime copy does not match frozen identity for {run_id}")
    if tar_tree_digest(runtime / "target") != target["tree_sha256"]:
        raise ValueError(f"target runtime copy does not match frozen identity for {run_id}")
    package_bytes = byte_tree_digest(runtime / "package")
    target_bytes = byte_tree_digest(runtime / "target")
    if package_bytes != byte_tree_digest(package_source):
        raise ValueError(f"package runtime copy differs for {run_id}")
    if target_bytes != byte_tree_digest(target_source):
        raise ValueError(f"target runtime copy differs for {run_id}")
    expected_allowlist = frozen_file_digest(
        FREEZE / "allowlists" / f"{target['mode']}.txt"
    )
    if sha256_file(runtime / "allowlist.txt") != expected_allowlist:
        raise ValueError(f"allowlist runtime copy differs from frozen bytes for {run_id}")
    attestation = {
        "schema_version": 1,
        "run_id": run_id,
        "cell_id": row["cell_id"],
        "runtime_root": str(runtime),
        "package_byte_tree_sha256": package_bytes,
        "target_byte_tree_sha256": target_bytes,
        "allowlist_sha256": expected_allowlist,
        "report_prompt_sha256": sha256_bytes(render_report_prompt(run_id, runtime).encode()),
        "output_initially_empty": True,
        "prepared_utc": utc_now(),
    }
    setup_path = COLLECTION / "setups" / f"{run_id}.json"
    write_once(setup_path, json_dump(attestation))
    setup_path.chmod(0o444)
    make_read_only(runtime / "package")
    make_read_only(runtime / "target")
    os.utime(runtime / "allowlist.txt", (0, 0), follow_symlinks=False)
    (runtime / "allowlist.txt").chmod(0o444)
    os.utime(runtime, (0, 0), follow_symlinks=False)
    runtime.chmod(0o555)
    append_event(
        "collection",
        "cell_prepared",
        run_id=run_id,
        digest=sha256_file(setup_path),
        details={"cell_id": row["cell_id"]},
    )
    print(runtime)


def report_prompt_blocks() -> list[str]:
    template = read_frozen_text(FREEZE / "prompts" / "report.md")
    blocks = re.findall(r"```text\n(.*?)\n```", template, flags=re.DOTALL)
    if len(blocks) != 2:
        raise ValueError("report prompt template must contain prompt and reminder fences")
    return blocks


def report_reminder_text() -> str:
    return report_prompt_blocks()[1]


def render_report_prompt(run_id: str, runtime: Path) -> str:
    _row, target, _condition = resolve_run(run_id)
    prompt = report_prompt_blocks()[0]
    replacements = {
        "[PACKAGE]": str(runtime / "package"),
        "[TARGET]": str(runtime / "target"),
        "[URL_ALLOWLIST]": str(runtime / "allowlist.txt"),
        "[OUTPUT]": str(runtime / "output"),
        "[WORD_LIMIT]": target["word_cap"],
    }
    for old, new in replacements.items():
        prompt = prompt.replace(old, new)
    if re.search(r"\[[A-Z_]+\]", prompt):
        raise ValueError("unresolved report-prompt placeholder")
    return prompt


def verify_runtime(run_id: str, runtime: Path, *, allow_invalid_output: bool = False) -> None:
    setup_path = COLLECTION / "setups" / f"{run_id}.json"
    prepared = [
        event
        for event in event_records()
        if event["event"] == "cell_prepared" and event.get("run_id") == run_id
    ]
    if len(prepared) != 1 or prepared[0].get("sha256") != sha256_file(setup_path):
        raise ValueError(f"setup attestation changed for {run_id}")
    setup = json.loads(setup_path.read_text())
    row, _target, _condition = resolve_run(run_id)
    expected_runtime = Path("/tmp/ur-eval") / row["cell_id"]
    if runtime != expected_runtime or runtime != Path(setup["runtime_root"]):
        raise ValueError(f"runtime is not bound to frozen cell {run_id}")
    if runtime.is_symlink() or not runtime.is_dir():
        raise ValueError(f"runtime root is not a real directory: {runtime}")
    if runtime.stat().st_mode & 0o222:
        raise ValueError(f"runtime root is writable: {runtime}")
    required_inputs = {"package", "target", "allowlist.txt"}
    expected_entries = required_inputs | {"output"}
    actual_entries = {entry.name for entry in runtime.iterdir()}
    if (
        (not allow_invalid_output and actual_entries != expected_entries)
        or (allow_invalid_output and (not required_inputs <= actual_entries or actual_entries - expected_entries))
    ):
        raise ValueError(f"runtime root inventory changed for {run_id}")
    allowlist = runtime / "allowlist.txt"
    output = runtime / "output"
    if allowlist.is_symlink() or not stat.S_ISREG(allowlist.lstat().st_mode):
        raise ValueError(f"runtime allowlist is not a real file: {run_id}")
    if not allow_invalid_output and (
        not output.exists()
        or output.is_symlink()
        or not stat.S_ISDIR(output.lstat().st_mode)
    ):
        raise ValueError(f"runtime output is not a real directory: {run_id}")
    checks = {
        "package_byte_tree_sha256": byte_tree_digest(runtime / "package"),
        "target_byte_tree_sha256": byte_tree_digest(runtime / "target"),
        "allowlist_sha256": sha256_file(allowlist),
        "report_prompt_sha256": sha256_bytes(render_report_prompt(run_id, runtime).encode()),
    }
    for field, actual in checks.items():
        if setup[field] != actual:
            raise ValueError(f"runtime input changed for {run_id}: {field}")


def observe_path(path: Path) -> dict[str, Any]:
    observation: dict[str, Any] = {"path": str(path)}
    try:
        mode = path.lstat().st_mode
    except FileNotFoundError:
        observation["type"] = "missing"
        return observation
    observation["mode"] = stat.S_IMODE(mode)
    if stat.S_ISLNK(mode):
        observation.update({"type": "symlink", "target": os.readlink(path)})
    elif stat.S_ISREG(mode):
        data = path.read_bytes()
        observation.update(
            {"type": "file", "bytes": len(data), "sha256": sha256_bytes(data)}
        )
    elif stat.S_ISDIR(mode):
        observation["type"] = "directory"
        observation["entries"] = sorted(entry.name for entry in path.iterdir())
        try:
            observation["byte_tree_sha256"] = byte_tree_digest(path)
        except (OSError, ValueError) as error:
            observation["byte_tree_error"] = f"{type(error).__name__}: {error}"
        else:
            try:
                observation["tar_tree_sha256"] = tar_tree_digest(path)
            except (OSError, subprocess.SubprocessError, ValueError) as error:
                observation["tar_tree_error"] = f"{type(error).__name__}: {error}"
    else:
        observation.update({"type": "special", "file_type": stat.S_IFMT(mode)})
    return observation


def report_runtime_forensics(run_id: str, runtime: Path, error: Exception) -> dict[str, Any]:
    row, target, condition = resolve_run(run_id)
    expected_runtime = Path("/tmp/ur-eval") / row["cell_id"]
    if runtime != expected_runtime:
        raise ValueError(f"forensic runtime is not the frozen neutral path {expected_runtime}")
    setup_path = COLLECTION / "setups" / f"{run_id}.json"
    prepared = [
        event
        for event in event_records()
        if event["event"] == "cell_prepared" and event.get("run_id") == run_id
    ]
    return {
        "schema_version": 1,
        "run_id": run_id,
        "verification_error": f"{type(error).__name__}: {error}",
        "expected": {
            "runtime_root": str(expected_runtime),
            "setup_sha256": prepared[0].get("sha256") if len(prepared) == 1 else None,
            "package_tar_tree_sha256": condition["tree_sha256"],
            "target_tar_tree_sha256": target["tree_sha256"],
            "allowlist_sha256": frozen_file_digest(
                FREEZE / "allowlists" / f"{target['mode']}.txt"
            ),
        },
        "observed": {
            "runtime_root": observe_path(runtime),
            "setup": observe_path(setup_path),
            "package": observe_path(runtime / "package")
            if runtime.exists() and not runtime.is_symlink() and runtime.is_dir()
            else {"type": "unavailable"},
            "target": observe_path(runtime / "target")
            if runtime.exists() and not runtime.is_symlink() and runtime.is_dir()
            else {"type": "unavailable"},
            "allowlist": observe_path(runtime / "allowlist.txt")
            if runtime.exists() and not runtime.is_symlink() and runtime.is_dir()
            else {"type": "unavailable"},
        },
    }


def append_event(
    phase: str,
    event: str,
    *,
    run_id: str | None = None,
    attempt: int | None = None,
    agent_id: str | None = None,
    digest: str | None = None,
    details: dict[str, Any] | None = None,
) -> None:
    path = RUN / "events.jsonl"
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a+", encoding="utf-8", newline="") as file:
        fcntl.flock(file, fcntl.LOCK_EX)
        file.seek(0)
        lines = file.read().splitlines()
        sequence = len(lines) + 1
        record: dict[str, Any] = {
            "schema_version": 1,
            "sequence": sequence,
            "previous_event_sha256": sha256_bytes(lines[-1].encode()) if lines else None,
            "time_utc": utc_now(),
            "phase": phase,
            "event": event,
            "details": details or {},
        }
        if run_id is not None:
            record["run_id"] = run_id
        if attempt is not None:
            record["attempt"] = attempt
        if agent_id is not None:
            record["agent_id"] = agent_id
        if digest is not None:
            record["sha256"] = digest
        validate_event_record(record, sequence)
        file.seek(0, os.SEEK_END)
        file.write(json.dumps(record, sort_keys=True) + "\n")
        file.flush()
        os.fsync(file.fileno())
        fcntl.flock(file, fcntl.LOCK_UN)


def validate_event_ledger() -> None:
    path = RUN / "events.jsonl"
    if not path.exists():
        return
    previous: str | None = None
    for index, line in enumerate(path.read_text().splitlines(), start=1):
        value = json.loads(line)
        validate_event_record(value, index)
        if value.get("previous_event_sha256") != previous:
            raise ValueError(f"broken event hash chain at line {index}")
        previous = sha256_bytes(line.encode())


def validate_event_record(value: Any, expected_sequence: int) -> None:
    required = {
        "schema_version",
        "sequence",
        "previous_event_sha256",
        "time_utc",
        "phase",
        "event",
        "details",
    }
    optional = {"run_id", "attempt", "agent_id", "sha256"}
    if not isinstance(value, dict) or not required <= set(value) or not set(value) <= required | optional:
        raise ValueError(f"invalid event fields at sequence {expected_sequence}")
    if (
        type(value["schema_version"]) is not int
        or value["schema_version"] != 1
        or type(value["sequence"]) is not int
        or value["sequence"] != expected_sequence
    ):
        raise ValueError(f"invalid event sequence {expected_sequence}")
    previous = value["previous_event_sha256"]
    if previous is not None and (
        not isinstance(previous, str) or not re.fullmatch(r"[0-9a-f]{64}", previous)
    ):
        raise ValueError(f"invalid prior-event hash at sequence {expected_sequence}")
    if not isinstance(value["time_utc"], str):
        raise ValueError(f"invalid event timestamp at sequence {expected_sequence}")
    try:
        parsed_time = datetime.fromisoformat(value["time_utc"].replace("Z", "+00:00"))
    except (AttributeError, ValueError) as error:
        raise ValueError(f"invalid event timestamp at sequence {expected_sequence}") from error
    if parsed_time.tzinfo is None:
        raise ValueError(f"event timestamp lacks timezone at sequence {expected_sequence}")
    if (
        not isinstance(value["phase"], str)
        or value["phase"] not in EVENT_PHASES
        or not isinstance(value["event"], str)
        or not value["event"]
    ):
        raise ValueError(f"invalid event identity at sequence {expected_sequence}")
    if not isinstance(value["details"], dict):
        raise ValueError(f"invalid event details at sequence {expected_sequence}")
    if "run_id" in value and (not isinstance(value["run_id"], str) or not value["run_id"]):
        raise ValueError(f"invalid event run ID at sequence {expected_sequence}")
    if "attempt" in value and (
        not isinstance(value["attempt"], int)
        or isinstance(value["attempt"], bool)
        or value["attempt"] < 1
    ):
        raise ValueError(f"invalid event attempt at sequence {expected_sequence}")
    if "agent_id" in value and (
        not is_nonblank_string(value["agent_id"])
        or value["agent_id"] != value["agent_id"].strip()
    ):
        raise ValueError(f"invalid event agent ID at sequence {expected_sequence}")
    if "sha256" in value and (
        not isinstance(value["sha256"], str) or not re.fullmatch(r"[0-9a-f]{64}", value["sha256"])
    ):
        raise ValueError(f"invalid event digest at sequence {expected_sequence}")


def validate_preserved_artifacts() -> None:
    events = event_records()
    attempt_events: dict[tuple[str, int], dict[str, Any]] = {}
    evaluator_attempt_events: dict[tuple[str, str, int], dict[str, Any]] = {}
    invalid_output_events: dict[tuple[str, str, int], dict[str, Any]] = {}
    for event in events:
        if event["event"] == "attempt_preserved":
            key = (event["run_id"], event["attempt"])
            if key in attempt_events:
                raise ValueError(f"duplicate attempt-preservation event: {key}")
            attempt_events[key] = event
            directory = (
                COLLECTION
                / "attempts"
                / event["run_id"]
                / str(event["attempt"])
            )
            if byte_tree_digest(directory) != event.get("sha256"):
                raise ValueError(
                    f"preserved attempt changed: {event['run_id']}/{event['attempt']}"
                )
        elif event["event"] == "invalid_output_preserved":
            details = event.get("details", {})
            kind = details.get("kind")
            if kind not in {"scorer", "adjudicator"}:
                raise ValueError("invalid preserved-output evaluator kind")
            phase = "scoring" if kind == "scorer" else "adjudication"
            identity = details.get("identity")
            key = (phase, str(identity), event["attempt"])
            if event["phase"] != phase or key in invalid_output_events:
                raise ValueError(f"duplicate or misphased invalid-output event: {key}")
            invalid_output_events[key] = event
            directory = (
                SCORING
                / "invalid"
                / phase
                / str(identity)
                / str(event.get("attempt"))
            )
            if byte_tree_digest(directory) != event.get("sha256"):
                raise ValueError(f"preserved invalid output changed: {directory}")
        elif event["event"] == "evaluator_attempt_preserved":
            details = event.get("details", {})
            kind = details.get("kind")
            if kind not in {"scorer", "adjudicator"}:
                raise ValueError("invalid preserved-attempt evaluator kind")
            phase = "scoring" if kind == "scorer" else "adjudication"
            identity = details.get("identity")
            key = (phase, str(identity), event["attempt"])
            if event["phase"] != phase or key in evaluator_attempt_events:
                raise ValueError(f"duplicate or misphased evaluator-attempt event: {key}")
            evaluator_attempt_events[key] = event
            directory = (
                SCORING
                / "evaluator-attempts"
                / phase
                / str(identity)
                / str(event.get("attempt"))
            )
            if byte_tree_digest(directory) != event.get("sha256"):
                raise ValueError(f"preserved evaluator attempt changed: {directory}")
        elif event["event"] == "freeze_locked":
            if (
                sha256_file(FILE_MANIFEST) != event.get("sha256")
                or sha256_file(LOCK) != event.get("details", {}).get("lock_sha256")
            ):
                raise ValueError("freeze-lock artifacts changed")
        elif event["event"] == "authority_verified":
            if frozen_file_digest(FREEZE / "authority-manifest.tsv") != event.get("sha256"):
                raise ValueError("authority verification event has the wrong manifest")
        elif event["event"] == "report_preserved":
            report = (
                COLLECTION
                / "attempts"
                / event["run_id"]
                / str(event["attempt"])
                / "report.md"
            )
            if sha256_file(report) != event.get("sha256"):
                raise ValueError(f"preserved report changed: {event['run_id']}")
        elif event["event"] == "collection_locked":
            if sha256_file(COLLECTION / "valid-index.jsonl") != event.get("sha256"):
                raise ValueError("locked collection index changed")
        elif event["event"] == "blind_packet_preserved":
            details = event.get("details", {})
            packet = SCORING / "packets" / str(details.get("mode")) / str(
                details.get("scorer")
            )
            if byte_tree_digest(packet) != event.get("sha256"):
                raise ValueError(f"preserved blind packet changed: {packet}")
        elif event["event"] == "score_preserved":
            details = event.get("details", {})
            score = SCORING / "raw" / str(details.get("mode")) / (
                str(details.get("scorer")) + ".json"
            )
            if sha256_file(score) != event.get("sha256"):
                raise ValueError(f"preserved score changed: {score}")
        elif event["event"] == "disagreements_materialized":
            path = SCORING / "disagreements" / (
                str(event.get("details", {}).get("mode")) + ".json"
            )
            if sha256_file(path) != event.get("sha256"):
                raise ValueError(f"preserved disagreements changed: {path}")
        elif event["event"] == "adjudication_packet_preserved":
            packet = SCORING / "adjudication-packets" / str(
                event.get("details", {}).get("mode")
            )
            if byte_tree_digest(packet) != event.get("sha256"):
                raise ValueError(f"preserved adjudication packet changed: {packet}")
        elif event["event"] == "adjudication_preserved":
            path = SCORING / "adjudications" / (
                str(event.get("details", {}).get("mode")) + ".json"
            )
            if sha256_file(path) != event.get("sha256"):
                raise ValueError(f"preserved adjudication changed: {path}")
        elif event["event"] == "final_blind_score_locked":
            path = SCORING / "final" / (
                str(event.get("details", {}).get("mode")) + ".json"
            )
            if sha256_file(path) != event.get("sha256"):
                raise ValueError(f"final blind score changed: {path}")
        elif event["event"] == "conditions_revealed":
            if sha256_file(RUN / "unblinding.json") != event.get("sha256"):
                raise ValueError("unblinding artifact changed")
        elif event["event"] == "aggregate_written":
            if (
                sha256_file(RESULTS / "aggregate.json") != event.get("sha256")
                or sha256_file(RESULTS / "summary.md")
                != event.get("details", {}).get("summary_sha256")
            ):
                raise ValueError("final result artifacts changed")
        elif event["event"] == "run_invalidated":
            if sha256_file(RUN / "INVALID.json") != event.get("sha256"):
                raise ValueError("INVALID marker changed")
    attempt_root = COLLECTION / "attempts"
    actual_attempts: set[tuple[str, int]] = set()
    if attempt_root.exists():
        for run_dir in attempt_root.iterdir():
            if run_dir.is_symlink() or not run_dir.is_dir():
                raise ValueError(f"invalid attempt run directory: {run_dir}")
            for attempt_dir in run_dir.iterdir():
                if (
                    attempt_dir.is_symlink()
                    or not attempt_dir.is_dir()
                    or not attempt_dir.name.isdigit()
                    or int(attempt_dir.name) < 1
                ):
                    raise ValueError(f"invalid attempt directory: {attempt_dir}")
                actual_attempts.add((run_dir.name, int(attempt_dir.name)))
    if actual_attempts != set(attempt_events):
        raise ValueError("attempt directories and preservation events differ")

    def inventory_evaluator_attempts(
        root: Path, expected: set[tuple[str, str, int]], label: str
    ) -> set[tuple[str, str, int]]:
        if root.is_symlink():
            raise ValueError(f"invalid {label} artifact root: {root}")
        if not root.exists():
            if expected:
                raise ValueError(f"missing {label} artifact root")
            return set()
        if not root.is_dir():
            raise ValueError(f"invalid {label} artifact root: {root}")
        if not expected:
            raise ValueError(f"orphan empty {label} artifact root: {root}")
        actual: set[tuple[str, str, int]] = set()
        actual_phases: set[str] = set()
        actual_identities: set[tuple[str, str]] = set()
        scorer_identities = {
            f"{mode}-{scorer}" for mode in MODES for scorer in SCORERS
        }
        for phase_dir in root.iterdir():
            if (
                phase_dir.is_symlink()
                or not phase_dir.is_dir()
                or phase_dir.name not in {"scoring", "adjudication"}
            ):
                raise ValueError(f"invalid {label} phase directory: {phase_dir}")
            phase = phase_dir.name
            actual_phases.add(phase)
            for identity_dir in phase_dir.iterdir():
                identity = identity_dir.name
                valid_identity = (
                    identity in scorer_identities if phase == "scoring" else identity in MODES
                )
                if identity_dir.is_symlink() or not identity_dir.is_dir() or not valid_identity:
                    raise ValueError(f"invalid {label} identity directory: {identity_dir}")
                actual_identities.add((phase, identity))
                for attempt_dir in identity_dir.iterdir():
                    if (
                        attempt_dir.is_symlink()
                        or not attempt_dir.is_dir()
                        or not re.fullmatch(r"[1-9][0-9]*", attempt_dir.name)
                    ):
                        raise ValueError(f"invalid {label} attempt directory: {attempt_dir}")
                    actual.add((phase, identity, int(attempt_dir.name)))
        expected_phases = {phase for phase, _identity, _attempt in expected}
        expected_identities = {(phase, identity) for phase, identity, _attempt in expected}
        if actual_phases != expected_phases or actual_identities != expected_identities:
            raise ValueError(f"{label} directory hierarchy differs from preservation events")
        return actual

    actual_evaluator_attempts = inventory_evaluator_attempts(
        SCORING / "evaluator-attempts",
        set(evaluator_attempt_events),
        "evaluator-attempt",
    )
    if actual_evaluator_attempts != set(evaluator_attempt_events):
        raise ValueError("evaluator-attempt directories and preservation events differ")
    actual_invalid_outputs = inventory_evaluator_attempts(
        SCORING / "invalid", set(invalid_output_events), "invalid-output"
    )
    if actual_invalid_outputs != set(invalid_output_events):
        raise ValueError("invalid-output directories and preservation events differ")
    if set(evaluator_attempt_events) & set(invalid_output_events):
        raise ValueError("one evaluator attempt has both valid/infra and invalid preservation")

    invalidated = [event for event in events if event["event"] == "run_invalidated"]
    invalid_returns = [
        event
        for event in events
        if event["event"] == "evaluator_returned"
        and event.get("details", {}).get("api_state") == "INVALID_OUTPUT"
    ]
    invalid_marker = RUN / "INVALID.json"
    if not invalid_output_events:
        if invalid_marker.exists() or invalid_marker.is_symlink() or invalidated or invalid_returns:
            raise ValueError("INVALID marker or terminal-invalid events lack an invalid output")
    else:
        if len(invalid_output_events) != 1 or len(invalidated) != 1 or len(invalid_returns) != 1:
            raise ValueError("terminal-invalid evaluator state is not unique and complete")
        if invalid_marker.is_symlink() or not invalid_marker.is_file():
            raise ValueError("terminal-invalid event lacks a real INVALID marker")
        key, invalid_event = next(iter(invalid_output_events.items()))
        phase, identity, attempt = key
        invalid_directory = SCORING / "invalid" / phase / identity / str(attempt)
        attestation = json.loads((invalid_directory / "attestation.json").read_text())
        marker = json.loads(invalid_marker.read_text())
        if marker != attestation:
            raise ValueError("INVALID marker differs from the invalid-output attestation")
        if (
            marker.get("phase") != phase
            or marker.get("identity") != identity
            or marker.get("attempt") != attempt
            or marker.get("agent_id") != invalid_event.get("agent_id")
            or marker.get("disposition") != "INVALID_NONRERUNNABLE_EVALUATOR_OUTPUT"
        ):
            raise ValueError("terminal-invalid attestation identity is inconsistent")
        invalidated_event = invalidated[0]
        if (
            invalidated_event.get("phase") != phase
            or invalidated_event.get("attempt") != attempt
            or invalidated_event.get("agent_id") != marker.get("agent_id")
            or invalidated_event.get("sha256") != sha256_file(invalid_marker)
            or invalidated_event.get("details")
            != {"identity": identity, "evidence": marker.get("evidence")}
        ):
            raise ValueError("run-invalidated event differs from the INVALID marker")
        returned = invalid_returns[0]
        expected_kind = "scorer" if phase == "scoring" else "adjudicator"
        if (
            returned.get("phase") != phase
            or returned.get("attempt") != attempt
            or returned.get("agent_id") != marker.get("agent_id")
            or returned.get("details")
            != {"kind": expected_kind, "identity": identity, "api_state": "INVALID_OUTPUT"}
        ):
            raise ValueError("invalid evaluator-return event is inconsistent")

    setup_root = COLLECTION / "setups"
    actual_setups: set[str] = set()
    if setup_root.exists():
        for path in setup_root.iterdir():
            if path.is_symlink() or not path.is_file() or path.suffix != ".json":
                raise ValueError(f"invalid setup artifact: {path}")
            actual_setups.add(path.stem)
    prepared = {
        event["run_id"]: event
        for event in events
        if event["event"] == "cell_prepared"
    }
    if len(prepared) != sum(event["event"] == "cell_prepared" for event in events):
        raise ValueError("duplicate cell-preparation event")
    if actual_setups != set(prepared):
        raise ValueError("cell setup files and preparation events differ")
    for run_id, event in prepared.items():
        if sha256_file(setup_root / f"{run_id}.json") != event.get("sha256"):
            raise ValueError(f"cell setup changed: {run_id}")


def append_report_index(metadata: dict[str, Any]) -> None:
    path = COLLECTION / "valid-index.jsonl"
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a+", encoding="utf-8", newline="") as file:
        fcntl.flock(file, fcntl.LOCK_EX)
        file.seek(0)
        existing = [json.loads(line) for line in file.read().splitlines()]
        if any(item["run_id"] == metadata["run_id"] for item in existing):
            raise ValueError(f"canonical report already indexed for {metadata['run_id']}")
        file.seek(0, os.SEEK_END)
        file.write(json.dumps(metadata, sort_keys=True) + "\n")
        file.flush()
        os.fsync(file.fileno())
        fcntl.flock(file, fcntl.LOCK_UN)


def output_entries(output: Path) -> list[Path]:
    if not output.exists() or output.is_symlink() or not stat.S_ISDIR(output.lstat().st_mode):
        raise ValueError(f"output path is not a real directory: {output}")
    entries = sorted(output.iterdir(), key=lambda path: path.name) if output.exists() else []
    for entry in entries:
        mode = entry.lstat().st_mode
        if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
            raise ValueError(f"unsupported output entry: {entry}")
    return entries


def snapshot_path(source: Path, raw_root: Path) -> list[dict[str, Any]]:
    """Preserve every regular byte reachable without following a symlink."""
    raw_root.mkdir(parents=True, exist_ok=True)
    records: list[dict[str, Any]] = []
    try:
        root_mode = source.lstat().st_mode
    except FileNotFoundError:
        return [{"path": ".", "type": "missing"}]
    if stat.S_ISLNK(root_mode):
        return [{"path": ".", "type": "symlink", "target": os.readlink(source)}]
    if stat.S_ISREG(root_mode):
        data = source.read_bytes()
        stored = "__output_path_file__"
        write_bytes_once(raw_root / stored, data)
        return [
            {
                "path": ".",
                "type": "file",
                "stored_as": stored,
                "bytes": len(data),
                "sha256": sha256_bytes(data),
            }
        ]
    if not stat.S_ISDIR(root_mode):
        return [{"path": ".", "type": "special", "mode": stat.S_IFMT(root_mode)}]

    records.append({"path": ".", "type": "directory"})

    def walk(directory: Path, relative: Path) -> None:
        with os.scandir(directory) as iterator:
            entries = sorted(iterator, key=lambda entry: entry.name)
        for entry in entries:
            child_relative = relative / entry.name
            rendered = child_relative.as_posix()
            mode = entry.stat(follow_symlinks=False).st_mode
            source_child = directory / entry.name
            destination_child = raw_root / child_relative
            if stat.S_ISREG(mode):
                data = source_child.read_bytes()
                write_bytes_once(destination_child, data)
                records.append(
                    {
                        "path": rendered,
                        "type": "file",
                        "bytes": len(data),
                        "sha256": sha256_bytes(data),
                    }
                )
            elif stat.S_ISDIR(mode):
                destination_child.mkdir()
                records.append({"path": rendered, "type": "directory"})
                walk(source_child, child_relative)
            elif stat.S_ISLNK(mode):
                records.append(
                    {"path": rendered, "type": "symlink", "target": os.readlink(source_child)}
                )
            else:
                records.append(
                    {"path": rendered, "type": "special", "mode": stat.S_IFMT(mode)}
                )

    walk(source, Path())
    return records


def preserve_captured_file(raw_root: Path, filename: str, data: bytes) -> list[dict[str, Any]]:
    """Preserve already-captured bytes as an exact one-file output snapshot."""
    if Path(filename).name != filename or filename in {"", ".", ".."}:
        raise ValueError(f"invalid captured output filename: {filename}")
    raw_root.mkdir(parents=True, exist_ok=False)
    write_bytes_once(raw_root / filename, data)
    return [
        {"path": ".", "type": "directory"},
        {
            "path": filename,
            "type": "file",
            "bytes": len(data),
            "sha256": sha256_bytes(data),
        },
    ]


def record_report(
    run_id: str,
    attempt: int,
    runtime: Path,
    agent_id: str,
    scope_deviation: bool,
    scope_evidence: str,
) -> None:
    if scope_deviation and not scope_evidence.strip():
        raise ValueError("scope deviation requires nonempty evidence")
    assert_agent_started(run_id, attempt, agent_id)
    verify_runtime(run_id, runtime)
    output = runtime / "output"
    if not output.exists() or output.is_symlink() or not stat.S_ISDIR(output.lstat().st_mode):
        raise ValueError(f"output path is not a real directory: {output}")
    entries = output_entries(output)
    if [entry.name for entry in entries] != ["report.md"]:
        raise ValueError(f"{run_id} output is not exactly one report.md")
    data = entries[0].read_bytes()
    text = data.decode("utf-8")
    if not text.strip():
        raise ValueError(f"{run_id} report.md is empty or whitespace-only")
    words = len(text.split())
    _row, target, _condition = resolve_run(run_id)
    destination = COLLECTION / "attempts" / run_id / str(attempt)
    if destination.exists():
        raise FileExistsError(f"attempt already preserved: {destination}")
    destination.mkdir(parents=True)
    write_bytes_once(destination / "report.md", data)
    metadata = {
        "schema_version": 1,
        "run_id": run_id,
        "attempt": attempt,
        "agent_id": agent_id,
        "report_sha256": sha256_bytes(data),
        "word_count": words,
        "word_cap": int(target["word_cap"]),
        "within_word_cap": words <= int(target["word_cap"]),
        "utf8": True,
        "canonical_for_scoring": True,
        "semantic_noncompletion": False,
        "terminal_disposition": "COMPLETE",
        "api_state": "COMPLETED",
        "operational_scope_deviation": scope_deviation,
        "scope_evidence": scope_evidence,
        "source_isolation": "procedural",
        "recorded_utc": utc_now(),
    }
    write_once(destination / "attestation.json", json_dump(metadata))
    append_report_index(metadata)
    make_read_only(destination)
    append_event(
        "collection",
        "attempt_preserved",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        digest=byte_tree_digest(destination),
        details={"disposition": "COMPLETE"},
    )
    append_event(
        "collection",
        "agent_returned",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        details={"api_state": "COMPLETED"},
    )
    append_event(
        "collection",
        "report_preserved",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        digest=metadata["report_sha256"],
        details={
            "word_count": words,
            "within_word_cap": metadata["within_word_cap"],
            "operational_scope_deviation": scope_deviation,
            "disposition": "COMPLETE",
        },
    )
    print(json_dump(metadata), end="")


def preserve_failed_report_attempt(
    run_id: str,
    attempt: int,
    runtime: Path,
    agent_id: str,
    disposition: str,
    evidence: str,
    scope_deviation: bool,
) -> None:
    if disposition not in INFRA_FAILURE_CODES | TERMINAL_REPORT_FAILURE_CODES:
        raise ValueError(f"unknown failure disposition: {disposition}")
    if not evidence.strip():
        raise ValueError("failed report disposition requires nonempty evidence")
    assert_agent_started(run_id, attempt, agent_id)
    forensics: dict[str, Any] | None = None
    try:
        verify_runtime(run_id, runtime, allow_invalid_output=True)
    except (OSError, ValueError) as error:
        forensics = report_runtime_forensics(run_id, runtime, error)
        disposition = "INVALID_OUTPUT"
        scope_deviation = True
        evidence = (
            f"{evidence} Runtime/input verification failed: "
            f"{forensics['verification_error']}"
        )
    output = runtime / "output"
    destination = COLLECTION / "attempts" / run_id / str(attempt)
    if destination.exists():
        raise FileExistsError(f"attempt already preserved: {destination}")
    if forensics is None:
        entry_manifest = snapshot_path(output, destination / "raw-output")
        manifest_path = destination / "raw-output-manifest.json"
        captured_report = destination / "raw-output" / "report.md"
    else:
        # A failed runtime check may have been caused by an unexpected root entry
        # or by drift in an input tree. Preserve the entire neutral runtime without
        # following symlinks, rather than retaining only the ordinary output path.
        entry_manifest = snapshot_path(runtime, destination / "raw-runtime")
        manifest_path = destination / "raw-runtime-manifest.json"
        setup = COLLECTION / "setups" / f"{run_id}.json"
        setup_manifest = snapshot_path(setup, destination / "setup-at-verification")
        write_once(
            destination / "setup-at-verification-manifest.json",
            json_dump(setup_manifest),
        )
        captured_report = destination / "raw-runtime" / "output" / "report.md"
    usable_report: bytes | None = None
    if (
        captured_report.exists()
        and not captured_report.is_symlink()
        and stat.S_ISREG(captured_report.lstat().st_mode)
    ):
        data = captured_report.read_bytes()
        try:
            data.decode("utf-8")
        except UnicodeDecodeError:
            pass
        else:
            usable_report = data
    write_once(manifest_path, json_dump(entry_manifest))
    if forensics is not None:
        write_once(destination / "runtime-forensics.json", json_dump(forensics))
    infrastructure = disposition in INFRA_FAILURE_CODES
    if infrastructure:
        metadata = {
            "schema_version": 1,
            "run_id": run_id,
            "attempt": attempt,
            "agent_id": agent_id,
            "terminal_disposition": disposition,
            "api_state": "INFRASTRUCTURE_FAILURE",
            "rerunnable": True,
            "evidence": evidence,
            "operational_scope_deviation": scope_deviation,
            "recorded_utc": utc_now(),
        }
        write_once(destination / "attestation.json", json_dump(metadata))
        make_read_only(destination)
        append_event(
            "collection",
            "attempt_preserved",
            run_id=run_id,
            attempt=attempt,
            agent_id=agent_id,
            digest=byte_tree_digest(destination),
            details={"disposition": disposition},
        )
        append_event(
            "collection",
            "agent_returned",
            run_id=run_id,
            attempt=attempt,
            agent_id=agent_id,
            details={"api_state": "INFRASTRUCTURE_FAILURE"},
        )
        append_event(
            "collection",
            "infrastructure_failure",
            run_id=run_id,
            attempt=attempt,
            agent_id=agent_id,
            details={"disposition": disposition, "evidence": evidence},
        )
        runtime.chmod(0o755)
        try:
            if output.is_symlink() or output.is_file():
                output.unlink()
            elif output.exists():
                shutil.rmtree(output)
            output.mkdir()
        finally:
            os.utime(runtime, (0, 0), follow_symlinks=False)
            runtime.chmod(0o555)
        print(json_dump(metadata), end="")
        return

    if usable_report is None:
        usable_report = (
            "# Evaluator-marked failed replicate\n\n"
            f"No usable canonical report was produced. Terminal disposition: {disposition}.\n"
        ).encode()
    text = usable_report.decode("utf-8")
    words = len(text.split())
    _row, target, _condition = resolve_run(run_id)
    write_bytes_once(destination / "report.md", usable_report)
    metadata = {
        "schema_version": 1,
        "run_id": run_id,
        "attempt": attempt,
        "agent_id": agent_id,
        "report_sha256": sha256_bytes(usable_report),
        "word_count": words,
        "word_cap": int(target["word_cap"]),
        "within_word_cap": words <= int(target["word_cap"]),
        "utf8": True,
        "canonical_for_scoring": True,
        "semantic_noncompletion": True,
        "terminal_disposition": disposition,
        "api_state": "TERMINAL_NONCOMPLETION",
        "operational_scope_deviation": scope_deviation or disposition == "INVALID_OUTPUT",
        "scope_evidence": evidence,
        "source_isolation": "procedural",
        "recorded_utc": utc_now(),
    }
    write_once(destination / "attestation.json", json_dump(metadata))
    append_report_index(metadata)
    make_read_only(destination)
    append_event(
        "collection",
        "attempt_preserved",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        digest=byte_tree_digest(destination),
        details={"disposition": disposition},
    )
    append_event(
        "collection",
        "agent_returned",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        details={"api_state": "TERMINAL_NONCOMPLETION"},
    )
    append_event(
        "collection",
        "report_preserved",
        run_id=run_id,
        attempt=attempt,
        agent_id=agent_id,
        digest=metadata["report_sha256"],
        details={"disposition": disposition, "semantic_noncompletion": True},
    )
    print(json_dump(metadata), end="")


def verify_collection_lock() -> None:
    path = COLLECTION / "valid-index.jsonl"
    matches = [event for event in event_records() if event["event"] == "collection_locked"]
    if len(matches) != 1 or matches[0].get("sha256") != sha256_file(path):
        raise ValueError("canonical collection index is not locked to the event ledger")
    if matches[0].get("details", {}).get("report_count") != 80:
        raise ValueError("collection lock has an invalid report count")


def load_index(*, require_collection_lock: bool = False) -> dict[str, dict[str, Any]]:
    path = COLLECTION / "valid-index.jsonl"
    if path.is_symlink() or not path.is_file():
        raise ValueError("canonical report index is not a real file")
    rows = [json.loads(line) for line in path.read_text().splitlines()]
    if any(not isinstance(row, dict) or not isinstance(row.get("run_id"), str) for row in rows):
        raise ValueError("canonical report index has an invalid row")
    result = {row["run_id"]: row for row in rows}
    if len(rows) != len(result):
        raise ValueError("duplicate canonical reports in index")
    if require_collection_lock:
        verify_collection_lock()
    for run_id, row in result.items():
        if (
            not isinstance(row, dict)
            or type(row.get("schema_version")) is not int
            or row["schema_version"] != 1
            or type(row.get("attempt")) is not int
            or row["attempt"] < 1
            or not isinstance(row.get("agent_id"), str)
            or not row["agent_id"]
            or not isinstance(row.get("report_sha256"), str)
            or not re.fullmatch(r"[0-9a-f]{64}", row["report_sha256"])
            or type(row.get("word_count")) is not int
            or row["word_count"] < 0
        ):
            raise ValueError(f"invalid canonical report index row for {run_id}")
        attempt = row["attempt"]
        directory = COLLECTION / "attempts" / run_id / str(attempt)
        report = directory / "report.md"
        attestation = json.loads((directory / "attestation.json").read_text())
        if attestation != row:
            raise ValueError(f"indexed attestation mismatch for {run_id}")
        if sha256_file(report) != row["report_sha256"]:
            raise ValueError(f"indexed report hash mismatch for {run_id}")
        text = report.read_bytes().decode("utf-8")
        if len(text.split()) != row["word_count"]:
            raise ValueError(f"indexed report word-count mismatch for {run_id}")
        preserved = [
            event
            for event in event_records()
            if event["event"] == "report_preserved"
            and event.get("run_id") == run_id
            and event.get("attempt") == attempt
        ]
        if len(preserved) != 1 or preserved[0].get("sha256") != row["report_sha256"]:
            raise ValueError(f"canonical report lacks its preservation event: {run_id}")
        attempts = [
            event
            for event in event_records()
            if event["event"] == "attempt_preserved"
            and event.get("run_id") == run_id
            and event.get("attempt") == attempt
        ]
        if len(attempts) != 1 or attempts[0].get("sha256") != byte_tree_digest(directory):
            raise ValueError(f"canonical attempt differs from its preservation event: {run_id}")
    return result


def presentation_order(mode: str, scorer: str) -> list[str]:
    claim = f"{mode}-{scorer}"
    rows = {
        row["claim"]: row
        for row in read_frozen_tsv(SEALED / "presentation-orders.tsv")
    }
    return rows[claim]["labels_in_order"].split(",")


def build_score_packets() -> None:
    validate_static(require_lock=True, announce=False)
    index = load_index()
    if set(index) != set(load_schedule()):
        raise ValueError("collection does not contain exactly all 80 scheduled reports")
    if any(event["event"] == "collection_locked" for event in event_records()):
        raise ValueError("collection was already locked")
    append_event(
        "collection",
        "collection_locked",
        digest=sha256_file(COLLECTION / "valid-index.jsonl"),
        details={"report_count": 80},
    )
    (COLLECTION / "valid-index.jsonl").chmod(0o444)
    verify_collection_lock()
    blind = load_blind_map()
    target_by_mode = {row["mode"]: row for row in load_target_map().values()}
    packet_root = SCORING / "packets"
    if packet_root.exists():
        raise FileExistsError("scorer packets already exist")
    packet_digests: dict[str, str] = {}
    for mode in MODES:
        target_source = EVALS / target_by_mode[mode]["source_path"]
        for scorer in SCORERS:
            packet = packet_root / mode / scorer
            (packet / "reports").mkdir(parents=True)
            shutil.copytree(target_source, packet / "target")
            shutil.copy2(FREEZE / "allowlists" / f"{mode}.txt", packet / "allowlist.txt")
            shutil.copy2(FREEZE / "rubrics" / "SCORER.md", packet / "SCORER.md")
            shutil.copy2(FREEZE / "rubrics" / f"{mode}.md", packet / "RUBRIC.md")
            shutil.copy2(FREEZE / "schemas" / "score.schema.json", packet / "score.schema.json")
            if tar_tree_digest(packet / "target") != target_by_mode[mode]["tree_sha256"]:
                raise ValueError(f"copied target lost its frozen identity: {mode}/{scorer}")
            frozen_copies = {
                packet / "allowlist.txt": FREEZE / "allowlists" / f"{mode}.txt",
                packet / "SCORER.md": FREEZE / "rubrics" / "SCORER.md",
                packet / "RUBRIC.md": FREEZE / "rubrics" / f"{mode}.md",
                packet / "score.schema.json": FREEZE / "schemas" / "score.schema.json",
            }
            for destination, source in frozen_copies.items():
                if sha256_file(destination) != frozen_file_digest(source):
                    raise ValueError(f"frozen packet input changed during copy: {destination}")
            report_hashes: dict[str, str] = {}
            for label, run_id in blind[mode].items():
                attempt = index[run_id]["attempt"]
                source = COLLECTION / "attempts" / run_id / str(attempt) / "report.md"
                if sha256_file(source) != index[run_id]["report_sha256"]:
                    raise ValueError(f"report changed before packet build: {run_id}")
                destination = packet / "reports" / f"{label}.md"
                shutil.copy2(source, destination)
                report_hashes[label] = sha256_file(destination)
                if report_hashes[label] != index[run_id]["report_sha256"]:
                    raise ValueError(f"report changed during packet copy: {run_id}")
            manifest = {
                "schema_version": 1,
                "mode": mode,
                "scorer_id": scorer,
                "presentation_order": presentation_order(mode, scorer),
                "report_sha256": report_hashes,
                "target_byte_tree_sha256": byte_tree_digest(packet / "target"),
                "allowlist_sha256": sha256_file(packet / "allowlist.txt"),
                "common_rules_sha256": sha256_file(packet / "SCORER.md"),
                "rubric_sha256": sha256_file(packet / "RUBRIC.md"),
                "schema_sha256": sha256_file(packet / "score.schema.json"),
            }
            write_once(packet / "PACKET.json", json_dump(manifest))
            make_read_only(packet)
            packet_digest = byte_tree_digest(packet)
            packet_digests[f"{mode}-{scorer}"] = packet_digest
            append_event(
                "scoring",
                "blind_packet_preserved",
                digest=packet_digest,
                details={"mode": mode, "scorer": scorer},
            )
    digest = sha256_bytes(json.dumps(packet_digests, sort_keys=True).encode())
    append_event(
        "scoring",
        "blind_packets_built",
        digest=digest,
        details={"packet_count": 16},
    )
    print("built 16 blind scorer packets")


def verify_score_packet(mode: str, scorer: str) -> None:
    verify_collection_lock()
    packet = SCORING / "packets" / mode / scorer
    manifest = json.loads((packet / "PACKET.json").read_text())
    if (
        type(manifest.get("schema_version")) is not int
        or manifest["schema_version"] != 1
        or manifest.get("mode") != mode
        or manifest.get("scorer_id") != scorer
    ):
        raise ValueError(f"score packet identity mismatch: {mode}/{scorer}")
    if manifest.get("presentation_order") != presentation_order(mode, scorer):
        raise ValueError(f"score packet presentation mismatch: {mode}/{scorer}")
    checks = {
        "target_byte_tree_sha256": byte_tree_digest(packet / "target"),
        "allowlist_sha256": sha256_file(packet / "allowlist.txt"),
        "common_rules_sha256": sha256_file(packet / "SCORER.md"),
        "rubric_sha256": sha256_file(packet / "RUBRIC.md"),
        "schema_sha256": sha256_file(packet / "score.schema.json"),
    }
    for field, actual in checks.items():
        if manifest.get(field) != actual:
            raise ValueError(f"score packet changed: {mode}/{scorer}/{field}")
    report_hashes = {
        label: sha256_file(packet / "reports" / f"{label}.md") for label in LABELS
    }
    if manifest.get("report_sha256") != report_hashes:
        raise ValueError(f"score packet reports changed: {mode}/{scorer}")
    expected_files = {
        "PACKET.json",
        "allowlist.txt",
        "RUBRIC.md",
        "SCORER.md",
        "score.schema.json",
        *(f"reports/{label}.md" for label in LABELS),
    }
    expected_files.update(
        path.relative_to(packet).as_posix()
        for path in (packet / "target").rglob("*")
        if path.is_file()
    )
    actual_files = {
        path.relative_to(packet).as_posix() for path in packet.rglob("*") if path.is_file()
    }
    if actual_files != expected_files:
        raise ValueError(f"score packet has unexpected files: {mode}/{scorer}")
    expected_packet_digest = preserved_digest(
        "blind_packet_preserved", mode=mode, scorer=scorer
    )
    if byte_tree_digest(packet) != expected_packet_digest:
        raise ValueError(f"score packet differs from its external preservation event: {mode}/{scorer}")


def render_packet_prompt(template_name: str, packet: Path, output: Path, **values: str) -> str:
    template = read_frozen_text(FREEZE / "prompts" / template_name)
    match = re.search(r"```text\n(.*?)\n```", template, flags=re.DOTALL)
    if not match:
        raise ValueError(f"{template_name} missing text fence")
    prompt = match.group(1).replace("[PACKET]", str(packet)).replace("[OUTPUT]", str(output))
    for key, value in values.items():
        prompt = prompt.replace(f"[{key}]", value)
    if re.search(r"\[[A-Z_]+\]", prompt):
        raise ValueError(f"unresolved placeholder in {template_name}")
    return prompt


def expected_evaluator_output(kind: str, identity: str, attempt: int) -> Path:
    if attempt < 1:
        raise ValueError("evaluator attempt must be positive")
    seeds = load_frozen_seeds()
    seed_name = "scorer" if kind == "scorer" else "presentation"
    token = prepare.keyed(
        f"{kind}-output-v2", seeds[seed_name], f"{identity}|{attempt}"
    )[:32]
    return Path("/tmp/ur-eval") / token / "output"


def expected_evaluator_packet(kind: str, identity: str, attempt: int) -> Path:
    return expected_evaluator_output(kind, identity, attempt).parent / "packet"


def expected_source_packet_digest(kind: str, identity: str) -> str:
    if kind == "scorer":
        mode, scorer = identity.split("-", 1)
        return preserved_digest("blind_packet_preserved", mode=mode, scorer=scorer)
    return preserved_digest("adjudication_packet_preserved", mode=identity)


def prepare_evaluator_runtime(
    kind: str, identity: str, attempt: int, source_packet: Path, output: Path
) -> Path:
    assert_evaluator_attempt_allowed(kind, identity, attempt)
    expected = expected_evaluator_output(kind, identity, attempt)
    if output != expected:
        raise ValueError(f"{kind} output must be the frozen neutral path {expected}")
    root = output.parent
    if root.exists():
        verify_evaluator_runtime(kind, identity, attempt, source_packet, output)
        if any(output.iterdir()):
            raise ValueError(f"existing {kind} prelaunch output is not empty")
        return expected_evaluator_packet(kind, identity, attempt)
    runtime_packet = expected_evaluator_packet(kind, identity, attempt)
    root.mkdir(parents=True)
    shutil.copytree(source_packet, runtime_packet)
    if byte_tree_digest(runtime_packet) != expected_source_packet_digest(kind, identity):
        raise ValueError(f"{kind} runtime packet differs from frozen packet")
    make_read_only(runtime_packet)
    output.mkdir()
    os.utime(root, (0, 0), follow_symlinks=False)
    root.chmod(0o555)
    return runtime_packet


def verify_evaluator_runtime(
    kind: str,
    identity: str,
    attempt: int,
    source_packet: Path,
    output: Path,
    *,
    allow_invalid_output: bool = False,
) -> None:
    if output != expected_evaluator_output(kind, identity, attempt):
        raise ValueError(f"non-neutral {kind} output path")
    root = output.parent
    if root.is_symlink() or not root.is_dir() or root.stat().st_mode & 0o222:
        raise ValueError(f"invalid {kind} runtime root")
    actual_entries = {entry.name for entry in root.iterdir()}
    if (
        (not allow_invalid_output and actual_entries != {"packet", "output"})
        or (
            allow_invalid_output
            and ("packet" not in actual_entries or actual_entries - {"packet", "output"})
        )
    ):
        raise ValueError(f"unexpected {kind} runtime inventory")
    if not allow_invalid_output and (
        not output.exists()
        or output.is_symlink()
        or not stat.S_ISDIR(output.lstat().st_mode)
    ):
        raise ValueError(f"invalid {kind} output directory")
    runtime_packet = expected_evaluator_packet(kind, identity, attempt)
    if byte_tree_digest(source_packet) != expected_source_packet_digest(kind, identity):
        raise ValueError(f"{kind} source packet changed")
    if byte_tree_digest(runtime_packet) != expected_source_packet_digest(kind, identity):
        raise ValueError(f"{kind} runtime packet changed")


def evaluator_runtime_forensics(
    kind: str,
    identity: str,
    attempt: int,
    source_packet: Path,
    output: Path,
    error: Exception,
) -> dict[str, Any]:
    expected_output = expected_evaluator_output(kind, identity, attempt)
    if output != expected_output:
        raise ValueError(f"forensic evaluator output is not the neutral path {expected_output}")
    root = output.parent
    root_is_real = root.exists() and not root.is_symlink() and root.is_dir()
    return {
        "schema_version": 1,
        "kind": kind,
        "identity": identity,
        "attempt": attempt,
        "verification_error": f"{type(error).__name__}: {error}",
        "expected": {
            "output": str(expected_output),
            "source_packet_byte_tree_sha256": expected_source_packet_digest(kind, identity),
        },
        "observed": {
            "source_packet": observe_path(source_packet),
            "runtime_root": observe_path(root),
            "packet": observe_path(root / "packet")
            if root_is_real
            else {"type": "unavailable"},
            "output": observe_path(output)
            if root_is_real
            else {"type": "unavailable"},
        },
    }


def validate_score(value: Any, mode: str, scorer: str) -> None:
    if (
        not isinstance(value, dict)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != 1
    ):
        raise ValueError("invalid score envelope")
    if set(value) != {"schema_version", "mode", "scorer_id", "reports", "ambiguities"}:
        raise ValueError("unexpected score fields")
    if value.get("mode") != mode or value.get("scorer_id") != scorer:
        raise ValueError("score mode or scorer mismatch")
    if not isinstance(value["ambiguities"], list) or any(
        not is_nonblank_string(item) for item in value["ambiguities"]
    ):
        raise ValueError("invalid score ambiguities")
    reports = value.get("reports")
    if (
        not isinstance(reports, list)
        or len(reports) != 10
        or any(not isinstance(report, dict) for report in reports)
    ):
        raise ValueError("score must contain ten reports")
    report_labels = [report.get("label") for report in reports]
    if any(not isinstance(label, str) for label in report_labels) or tuple(
        sorted(report_labels)
    ) != LABELS:
        raise ValueError("score labels must be exactly A-J")
    expected_atoms = set(atom_ids(mode))
    allowed_hard = set(hard_error_ids(mode))
    for report in reports:
        if set(report) != {
            "label",
            "atoms",
            "hard_errors",
            "proposal_laundering",
            "tcb_authority_defect",
            "visible_scope_defect",
            "novel_findings",
        }:
            raise ValueError("unexpected report-score fields")
        atoms = report.get("atoms")
        if (
            not isinstance(atoms, list)
            or any(not isinstance(atom, dict) for atom in atoms)
            or {atom.get("id") for atom in atoms} != expected_atoms
        ):
            raise ValueError(f"{mode}/{report.get('label')}: incomplete atom set")
        if len(atoms) != len(expected_atoms):
            raise ValueError(f"{mode}/{report.get('label')}: duplicate atom ID")
        for atom in atoms:
            if set(atom) != {"id", "decision", "evidence"}:
                raise ValueError("unexpected atom fields")
            if (
                atom.get("decision") not in {"PASS", "FAIL"}
                or not is_nonblank_string(atom.get("evidence"))
            ):
                raise ValueError("invalid atom decision")
        hard = report.get("hard_errors")
        if not isinstance(hard, list) or any(
            not isinstance(finding, dict) for finding in hard
        ):
            raise ValueError("hard_errors must be a list")
        hard_ids = [finding.get("id") for finding in hard]
        if len(hard_ids) != len(set(hard_ids)) or not set(hard_ids) <= allowed_hard:
            raise ValueError(f"invalid hard-error IDs: {hard_ids}")
        if any(
            not is_nonblank_string(finding.get("evidence"))
            for finding in hard
        ):
            raise ValueError("hard error lacks evidence")
        if any(set(finding) != {"id", "evidence"} for finding in hard):
            raise ValueError("unexpected hard-error fields")
        for field in ("proposal_laundering", "tcb_authority_defect", "visible_scope_defect"):
            flag = report.get(field)
            if not isinstance(flag, dict) or not isinstance(flag.get("present"), bool):
                raise ValueError(f"invalid {field} flag")
            if set(flag) != {"present", "evidence"} or not is_nonblank_string(
                flag.get("evidence")
            ):
                raise ValueError(f"invalid {field} evidence")
        novel = report.get("novel_findings")
        if not isinstance(novel, list) or any(
            not isinstance(finding, dict) for finding in novel
        ):
            raise ValueError("novel_findings must be a list")
        novel_ids = [finding.get("id") for finding in novel]
        if len(novel_ids) != len(set(novel_ids)) or any(
            not re.fullmatch(r"N[1-9][0-9]*", str(identifier)) for identifier in novel_ids
        ):
            raise ValueError("invalid novel-finding IDs")
        if any(
            not is_nonblank_string(finding.get("evidence"))
            for finding in novel
        ):
            raise ValueError("novel finding lacks evidence")
        if any(set(finding) != {"id", "evidence"} for finding in novel):
            raise ValueError("unexpected novel-finding fields")


def record_score(
    mode: str, scorer: str, attempt: int, output: Path, agent_id: str
) -> None:
    assert_evaluator_started("scorer", f"{mode}-{scorer}", attempt, agent_id)
    verify_score_packet(mode, scorer)
    verify_evaluator_runtime(
        "scorer",
        f"{mode}-{scorer}",
        attempt,
        SCORING / "packets" / mode / scorer,
        output,
    )
    source = output / "score.json"
    entries = output_entries(output)
    if [entry.name for entry in entries] != ["score.json"]:
        raise ValueError("scorer output is not exactly score.json")
    raw = source.read_bytes()
    value = json.loads(raw.decode("utf-8"))
    validate_score(value, mode, scorer)
    attempt_directory = (
        SCORING
        / "evaluator-attempts"
        / "scoring"
        / f"{mode}-{scorer}"
        / str(attempt)
    )
    entries = preserve_captured_file(attempt_directory / "raw-output", "score.json", raw)
    write_once(attempt_directory / "raw-output-manifest.json", json_dump(entries))
    attempt_attestation = {
        "schema_version": 1,
        "phase": "scoring",
        "kind": "scorer",
        "identity": f"{mode}-{scorer}",
        "attempt": attempt,
        "agent_id": agent_id,
        "disposition": "COMPLETE",
        "recorded_utc": utc_now(),
    }
    write_once(attempt_directory / "attestation.json", json_dump(attempt_attestation))
    make_read_only(attempt_directory)
    append_event(
        "scoring",
        "evaluator_attempt_preserved",
        attempt=attempt,
        agent_id=agent_id,
        digest=byte_tree_digest(attempt_directory),
        details={"kind": "scorer", "identity": f"{mode}-{scorer}", "disposition": "COMPLETE"},
    )
    destination = SCORING / "raw" / mode / f"{scorer}.json"
    write_bytes_once(destination, raw)
    destination.chmod(0o444)
    append_event(
        "scoring",
        "evaluator_returned",
        attempt=attempt,
        agent_id=agent_id,
        details={"kind": "scorer", "identity": f"{mode}-{scorer}", "api_state": "COMPLETED"},
    )
    append_event(
        "scoring",
        "score_preserved",
        attempt=attempt,
        agent_id=agent_id,
        digest=sha256_file(destination),
        details={"mode": mode, "scorer": scorer},
    )
    print(destination)


def report_by_label(score: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {report["label"]: report for report in score["reports"]}


def preserved_digest(event_name: str, **details: str) -> str:
    matches = [
        event
        for event in event_records()
        if event["event"] == event_name
        and all(event.get("details", {}).get(key) == value for key, value in details.items())
    ]
    if len(matches) != 1 or "sha256" not in matches[0]:
        raise ValueError(f"expected one preserved digest for {event_name} {details}")
    return matches[0]["sha256"]


def load_preserved_score(mode: str, scorer: str) -> dict[str, Any]:
    path = SCORING / "raw" / mode / f"{scorer}.json"
    expected = preserved_digest("score_preserved", mode=mode, scorer=scorer)
    if sha256_file(path) != expected:
        raise ValueError(f"raw score changed after preservation: {mode}/{scorer}")
    value = json.loads(path.read_text())
    validate_score(value, mode, scorer)
    return value


def evidence_for_hard(report: dict[str, Any], identifier: str) -> str:
    for finding in report["hard_errors"]:
        if finding["id"] == identifier:
            return finding["evidence"]
    return "No applicable hard error recorded."


def disagreement_cells(mode: str, s1: dict[str, Any], s2: dict[str, Any]) -> list[dict[str, Any]]:
    cells: list[dict[str, Any]] = []
    by_scorer = {"s1": report_by_label(s1), "s2": report_by_label(s2)}
    for label in LABELS:
        first = by_scorer["s1"][label]
        second = by_scorer["s2"][label]
        atoms1 = {atom["id"]: atom for atom in first["atoms"]}
        atoms2 = {atom["id"]: atom for atom in second["atoms"]}
        for atom in atom_ids(mode):
            if atoms1[atom]["decision"] != atoms2[atom]["decision"]:
                cells.append(
                    {
                        "label": label,
                        "field": f"atom:{atom}",
                        "s1": {"decision": atoms1[atom]["decision"], "evidence": atoms1[atom]["evidence"]},
                        "s2": {"decision": atoms2[atom]["decision"], "evidence": atoms2[atom]["evidence"]},
                    }
                )
        for identifier in hard_error_ids(mode):
            present1 = any(item["id"] == identifier for item in first["hard_errors"])
            present2 = any(item["id"] == identifier for item in second["hard_errors"])
            if present1 != present2:
                cells.append(
                    {
                        "label": label,
                        "field": f"hard_error:{identifier}",
                        "s1": {"decision": "PRESENT" if present1 else "ABSENT", "evidence": evidence_for_hard(first, identifier)},
                        "s2": {"decision": "PRESENT" if present2 else "ABSENT", "evidence": evidence_for_hard(second, identifier)},
                    }
                )
        for field in ("proposal_laundering", "tcb_authority_defect", "visible_scope_defect"):
            flag1 = first[field]
            flag2 = second[field]
            if flag1["present"] != flag2["present"]:
                cells.append(
                    {
                        "label": label,
                        "field": field,
                        "s1": {"decision": "PRESENT" if flag1["present"] else "ABSENT", "evidence": flag1["evidence"]},
                        "s2": {"decision": "PRESENT" if flag2["present"] else "ABSENT", "evidence": flag2["evidence"]},
                    }
                )
        for scorer, report, other in (("s1", first, "s2"), ("s2", second, "s1")):
            for finding in report["novel_findings"]:
                cells.append(
                    {
                        "label": label,
                        "field": f"novel:{scorer}:{finding['id']}",
                        scorer: {"decision": "PRESENT", "evidence": finding["evidence"]},
                        other: {"decision": "ABSENT", "evidence": "Not independently proposed; adjudicate the candidate on its merits."},
                    }
                )
    keys = [(cell["label"], cell["field"]) for cell in cells]
    if len(keys) != len(set(keys)):
        raise ValueError("duplicate disagreement field")
    return cells


def build_disagreements(mode: str) -> None:
    scores: dict[str, dict[str, Any]] = {}
    for scorer in SCORERS:
        scores[scorer] = load_preserved_score(mode, scorer)
    value = {"schema_version": 1, "mode": mode, "cells": disagreement_cells(mode, scores["s1"], scores["s2"])}
    destination = SCORING / "disagreements" / f"{mode}.json"
    write_once(destination, json_dump(value))
    destination.chmod(0o444)
    append_event(
        "adjudication",
        "disagreements_materialized",
        digest=sha256_file(destination),
        details={"mode": mode, "count": len(value["cells"])},
    )
    print(f"{mode}: {len(value['cells'])} disputed or novel cells")


def build_adjudication_packet(mode: str) -> None:
    disagreement_path = SCORING / "disagreements" / f"{mode}.json"
    if sha256_file(disagreement_path) != preserved_digest("disagreements_materialized", mode=mode):
        raise ValueError(f"disagreements changed before packet build: {mode}")
    disagreements = json.loads(disagreement_path.read_text())
    if not disagreements["cells"]:
        print(f"{mode}: no adjudication packet required")
        return
    packet = SCORING / "adjudication-packets" / mode
    if packet.exists():
        raise FileExistsError(f"adjudication packet exists: {packet}")
    (packet / "reports").mkdir(parents=True)
    source_packet = SCORING / "packets" / mode / "s1"
    verify_score_packet(mode, "s1")
    source_packet_digest = preserved_digest("blind_packet_preserved", mode=mode, scorer="s1")
    source_manifest = json.loads((source_packet / "PACKET.json").read_text())
    shutil.copytree(source_packet / "target", packet / "target")
    for name in ("allowlist.txt", "SCORER.md", "RUBRIC.md"):
        shutil.copy2(source_packet / name, packet / name)
    shutil.copy2(FREEZE / "schemas" / "adjudication.schema.json", packet / "adjudication.schema.json")
    shutil.copy2(disagreement_path, packet / "DISAGREEMENTS.json")
    disputed_labels = sorted({cell["label"] for cell in disagreements["cells"]})
    for label in disputed_labels:
        shutil.copy2(source_packet / "reports" / f"{label}.md", packet / "reports" / f"{label}.md")
        if (
            sha256_file(packet / "reports" / f"{label}.md")
            != source_manifest["report_sha256"][label]
        ):
            raise ValueError(f"adjudication report changed during copy: {mode}/{label}")
    target_row = next(row for row in load_target_map().values() if row["mode"] == mode)
    if tar_tree_digest(packet / "target") != target_row["tree_sha256"]:
        raise ValueError(f"adjudication target lost frozen identity: {mode}")
    if sha256_file(packet / "DISAGREEMENTS.json") != preserved_digest(
        "disagreements_materialized", mode=mode
    ):
        raise ValueError(f"adjudication disagreements changed during copy: {mode}")
    expected_copies = {
        "allowlist.txt": "allowlist_sha256",
        "SCORER.md": "common_rules_sha256",
        "RUBRIC.md": "rubric_sha256",
    }
    for name, field in expected_copies.items():
        if sha256_file(packet / name) != source_manifest[field]:
            raise ValueError(f"adjudication packet input changed during copy: {mode}/{name}")
    if sha256_file(packet / "adjudication.schema.json") != frozen_file_digest(
        FREEZE / "schemas" / "adjudication.schema.json"
    ):
        raise ValueError(f"adjudication schema changed during copy: {mode}")
    manifest = {
        "schema_version": 1,
        "mode": mode,
        "source_score_packet_sha256": source_packet_digest,
        "disputed_labels": disputed_labels,
        "disagreements_sha256": sha256_file(packet / "DISAGREEMENTS.json"),
        "report_sha256": {label: sha256_file(packet / "reports" / f"{label}.md") for label in disputed_labels},
        "target_byte_tree_sha256": byte_tree_digest(packet / "target"),
        "allowlist_sha256": sha256_file(packet / "allowlist.txt"),
        "common_rules_sha256": sha256_file(packet / "SCORER.md"),
        "rubric_sha256": sha256_file(packet / "RUBRIC.md"),
        "schema_sha256": sha256_file(packet / "adjudication.schema.json"),
    }
    write_once(packet / "PACKET.json", json_dump(manifest))
    make_read_only(packet)
    append_event(
        "adjudication",
        "adjudication_packet_preserved",
        digest=byte_tree_digest(packet),
        details={"mode": mode, "source_score_packet_sha256": source_packet_digest},
    )
    print(packet)


def verify_adjudication_packet(mode: str) -> None:
    packet = SCORING / "adjudication-packets" / mode
    manifest = json.loads((packet / "PACKET.json").read_text())
    disagreements = json.loads((packet / "DISAGREEMENTS.json").read_text())
    if (
        type(manifest.get("schema_version")) is not int
        or manifest["schema_version"] != 1
        or manifest.get("mode") != mode
        or disagreements.get("mode") != mode
    ):
        raise ValueError(f"adjudication packet identity mismatch: {mode}")
    verify_score_packet(mode, "s1")
    source_digest = preserved_digest("blind_packet_preserved", mode=mode, scorer="s1")
    if manifest.get("source_score_packet_sha256") != source_digest:
        raise ValueError(f"adjudication packet source binding changed: {mode}")
    checks = {
        "disagreements_sha256": sha256_file(packet / "DISAGREEMENTS.json"),
        "target_byte_tree_sha256": byte_tree_digest(packet / "target"),
        "allowlist_sha256": sha256_file(packet / "allowlist.txt"),
        "common_rules_sha256": sha256_file(packet / "SCORER.md"),
        "rubric_sha256": sha256_file(packet / "RUBRIC.md"),
        "schema_sha256": sha256_file(packet / "adjudication.schema.json"),
    }
    for field, actual in checks.items():
        if manifest.get(field) != actual:
            raise ValueError(f"adjudication packet changed: {mode}/{field}")
    labels = manifest.get("disputed_labels")
    expected_labels = sorted({cell["label"] for cell in disagreements.get("cells", [])})
    if not isinstance(labels, list) or labels != expected_labels:
        raise ValueError(f"adjudication packet disputed-label inventory changed: {mode}")
    report_hashes = {
        label: sha256_file(packet / "reports" / f"{label}.md") for label in labels
    }
    if manifest.get("report_sha256") != report_hashes:
        raise ValueError(f"adjudication reports changed: {mode}")
    expected_files = {
        "PACKET.json",
        "DISAGREEMENTS.json",
        "allowlist.txt",
        "RUBRIC.md",
        "SCORER.md",
        "adjudication.schema.json",
        *(f"reports/{label}.md" for label in labels),
    }
    expected_files.update(
        path.relative_to(packet).as_posix()
        for path in (packet / "target").rglob("*")
        if path.is_file()
    )
    actual_files = {
        path.relative_to(packet).as_posix() for path in packet.rglob("*") if path.is_file()
    }
    if actual_files != expected_files:
        raise ValueError(f"adjudication packet has unexpected files: {mode}")
    expected_packet_digest = preserved_digest("adjudication_packet_preserved", mode=mode)
    if byte_tree_digest(packet) != expected_packet_digest:
        raise ValueError(f"adjudication packet differs from its external event: {mode}")


def validate_adjudication(value: Any, mode: str) -> None:
    disagreement_path = SCORING / "disagreements" / f"{mode}.json"
    expected_digest = preserved_digest("disagreements_materialized", mode=mode)
    if sha256_file(disagreement_path) != expected_digest:
        raise ValueError(f"disagreements changed after preservation: {mode}")
    disagreements = json.loads(disagreement_path.read_text())
    expected = {(cell["label"], cell["field"]) for cell in disagreements["cells"]}
    if (
        not isinstance(value, dict)
        or type(value.get("schema_version")) is not int
        or value["schema_version"] != 1
        or value.get("mode") != mode
    ):
        raise ValueError("invalid adjudication envelope")
    if set(value) != {"schema_version", "mode", "decisions", "ambiguities"}:
        raise ValueError("unexpected adjudication fields")
    if not isinstance(value["ambiguities"], list) or any(
        not is_nonblank_string(item) for item in value["ambiguities"]
    ):
        raise ValueError("invalid adjudication ambiguities")
    decisions = value.get("decisions")
    if not isinstance(decisions, list) or any(
        not isinstance(decision, dict) for decision in decisions
    ):
        raise ValueError("adjudication decisions must be a list")
    if any(
        not isinstance(decision.get("label"), str)
        or not isinstance(decision.get("field"), str)
        for decision in decisions
    ):
        raise ValueError("adjudication decision identity is invalid")
    actual = {(decision.get("label"), decision.get("field")) for decision in decisions}
    if actual != expected or len(decisions) != len(expected):
        raise ValueError("adjudication does not resolve exactly every disputed cell")
    for decision in decisions:
        if set(decision) != {"label", "field", "decision", "evidence"}:
            raise ValueError("unexpected adjudication-decision fields")
        expected_values = {"PASS", "FAIL"} if decision["field"].startswith("atom:") else {"PRESENT", "ABSENT"}
        if (
            decision.get("decision") not in expected_values
            or not is_nonblank_string(decision.get("evidence"))
        ):
            raise ValueError("invalid adjudication decision")


def synthetic_score(mode: str, scorer: str) -> dict[str, Any]:
    reports: list[dict[str, Any]] = []
    for label in LABELS:
        reports.append(
            {
                "label": label,
                "atoms": [
                    {"id": atom, "decision": "PASS", "evidence": "Synthetic complete evidence."}
                    for atom in atom_ids(mode)
                ],
                "hard_errors": [],
                "proposal_laundering": {"present": False, "evidence": "No proposal laundering."},
                "tcb_authority_defect": {"present": False, "evidence": "No TCB or authority defect."},
                "visible_scope_defect": {"present": False, "evidence": "No visible source-scope defect."},
                "novel_findings": [],
            }
        )
    return {
        "schema_version": 1,
        "mode": mode,
        "scorer_id": scorer,
        "reports": reports,
        "ambiguities": [],
    }


def self_test() -> None:
    validate_static(require_lock=False)
    for mode in MODES:
        first = synthetic_score(mode, "s1")
        second = synthetic_score(mode, "s2")
        validate_score(first, mode, "s1")
        validate_score(second, mode, "s2")
        first_report = first["reports"][0]
        second_report = second["reports"][0]
        first_report["atoms"][0]["decision"] = "FAIL"
        first_report["hard_errors"] = [
            {"id": hard_error_ids(mode)[0], "evidence": "Synthetic hard-error evidence."}
        ]
        first_report["proposal_laundering"] = {"present": True, "evidence": "Synthetic flag evidence."}
        first_report["novel_findings"] = [{"id": "N1", "evidence": "Synthetic novel candidate."}]
        cells = disagreement_cells(mode, first, second)
        expected_fields = {
            f"atom:{atom_ids(mode)[0]}",
            f"hard_error:{hard_error_ids(mode)[0]}",
            "proposal_laundering",
            "novel:s1:N1",
        }
        if {cell["field"] for cell in cells} != expected_fields:
            raise AssertionError(f"{mode}: disagreement self-test failed")
        invalid = synthetic_score(mode, "s1")
        invalid["reports"][1]["label"] = "A"
        try:
            validate_score(invalid, mode, "s1")
        except ValueError:
            pass
        else:
            raise AssertionError(f"{mode}: duplicate label was accepted")
        invalid = synthetic_score(mode, "s1")
        invalid["reports"][0]["atoms"].pop()
        try:
            validate_score(invalid, mode, "s1")
        except ValueError:
            pass
        else:
            raise AssertionError(f"{mode}: incomplete atom set was accepted")
        invalid = synthetic_score(mode, "s1")
        invalid["schema_version"] = True
        try:
            validate_score(invalid, mode, "s1")
        except ValueError:
            pass
        else:
            raise AssertionError(f"{mode}: boolean schema version was accepted")
        invalid = synthetic_score(mode, "s1")
        invalid["reports"][0]["atoms"][0]["evidence"] = 1
        try:
            validate_score(invalid, mode, "s1")
        except ValueError:
            pass
        else:
            raise AssertionError(f"{mode}: non-string evidence was accepted")
        invalid = synthetic_score(mode, "s1")
        invalid["reports"][0]["atoms"][0]["evidence"] = "   "
        try:
            validate_score(invalid, mode, "s1")
        except ValueError:
            pass
        else:
            raise AssertionError(f"{mode}: whitespace-only evidence was accepted")
    schedule = load_schedule()
    for run_id, row in schedule.items():
        runtime = Path("/tmp/ur-eval") / row["cell_id"]
        prompt = render_report_prompt(run_id, runtime)
        if "[" + "PACKAGE]" in prompt or "[" + "WORD_LIMIT]" in prompt:
            raise AssertionError("unresolved report prompt")
    if report_reminder_text() != (
        "Complete now within the frozen word limit using only material already\n"
        "inspected; do not widen scope."
    ):
        raise AssertionError("frozen reminder extraction changed")
    if expected_evaluator_output("scorer", "S-s1", 1) == expected_evaluator_output(
        "scorer", "S-s1", 2
    ):
        raise AssertionError("evaluator attempts share a runtime path")
    assert_evaluator_attempt_allowed("scorer", "S-s1", 1, [])
    try:
        assert_evaluator_attempt_allowed("scorer", "S-s1", 2, [])
    except ValueError:
        pass
    else:
        raise AssertionError("evaluator retry without infrastructure failure was accepted")
    assert_evaluator_attempt_allowed(
        "scorer",
        "S-s1",
        2,
        [
            {
                "event": "evaluator_infrastructure_failure",
                "attempt": 1,
                "details": {"kind": "scorer", "identity": "S-s1"},
            }
        ],
    )
    invalid_event = {
        "schema_version": True,
        "sequence": 1,
        "previous_event_sha256": None,
        "time_utc": utc_now(),
        "phase": "freeze",
        "event": "synthetic",
        "details": {},
    }
    try:
        validate_event_record(invalid_event, 1)
    except ValueError:
        pass
    else:
        raise AssertionError("boolean event schema version was accepted")
    metadata_root = Path(tempfile.mkdtemp(prefix="ur-packet-self-test-", dir="/tmp"))
    try:
        nested = metadata_root / "nested"
        nested.mkdir()
        file = nested / "report.md"
        file.write_text("packet metadata self-test\n")
        make_read_only(metadata_root)
        for item in (metadata_root, nested, file):
            if item.stat().st_mtime_ns != 0:
                raise AssertionError(f"metadata timestamp was not normalized: {item}")
    finally:
        for item in sorted(metadata_root.rglob("*"), reverse=True):
            item.chmod(0o755 if item.is_dir() else 0o644)
        metadata_root.chmod(0o755)
        shutil.rmtree(metadata_root)
    print("protocol self-test passed")


def record_adjudication(
    mode: str, attempt: int, output: Path, agent_id: str
) -> None:
    assert_evaluator_started("adjudicator", mode, attempt, agent_id)
    verify_adjudication_packet(mode)
    verify_evaluator_runtime(
        "adjudicator",
        mode,
        attempt,
        SCORING / "adjudication-packets" / mode,
        output,
    )
    entries = output_entries(output)
    if [entry.name for entry in entries] != ["adjudication.json"]:
        raise ValueError("adjudicator output is not exactly adjudication.json")
    raw = entries[0].read_bytes()
    value = json.loads(raw.decode("utf-8"))
    validate_adjudication(value, mode)
    attempt_directory = (
        SCORING
        / "evaluator-attempts"
        / "adjudication"
        / mode
        / str(attempt)
    )
    raw_entries = preserve_captured_file(
        attempt_directory / "raw-output", "adjudication.json", raw
    )
    write_once(
        attempt_directory / "raw-output-manifest.json", json_dump(raw_entries)
    )
    attempt_attestation = {
        "schema_version": 1,
        "phase": "adjudication",
        "kind": "adjudicator",
        "identity": mode,
        "attempt": attempt,
        "agent_id": agent_id,
        "disposition": "COMPLETE",
        "recorded_utc": utc_now(),
    }
    write_once(attempt_directory / "attestation.json", json_dump(attempt_attestation))
    make_read_only(attempt_directory)
    append_event(
        "adjudication",
        "evaluator_attempt_preserved",
        attempt=attempt,
        agent_id=agent_id,
        digest=byte_tree_digest(attempt_directory),
        details={"kind": "adjudicator", "identity": mode, "disposition": "COMPLETE"},
    )
    destination = SCORING / "adjudications" / f"{mode}.json"
    write_bytes_once(destination, raw)
    destination.chmod(0o444)
    append_event(
        "adjudication",
        "evaluator_returned",
        attempt=attempt,
        agent_id=agent_id,
        details={"kind": "adjudicator", "identity": mode, "api_state": "COMPLETED"},
    )
    append_event(
        "adjudication",
        "adjudication_preserved",
        attempt=attempt,
        agent_id=agent_id,
        digest=sha256_file(destination),
        details={"mode": mode},
    )
    print(destination)


def record_invalid_evaluator(
    phase: str,
    identity: str,
    attempt: int,
    output: Path,
    agent_id: str,
    evidence: str,
) -> None:
    invalid_marker = RUN / "INVALID.json"
    if invalid_marker.exists():
        raise FileExistsError("run is already marked INVALID")
    if not evidence.strip():
        raise ValueError("invalid evaluator output requires nonempty evidence")
    kind = "scorer" if phase == "scoring" else "adjudicator"
    assert_evaluator_started(kind, identity, attempt, agent_id)
    if kind == "scorer":
        mode, scorer = identity.split("-", 1)
        source_packet = SCORING / "packets" / mode / scorer
    else:
        source_packet = SCORING / "adjudication-packets" / identity
    forensics: dict[str, Any] | None = None
    try:
        verify_evaluator_runtime(
            kind, identity, attempt, source_packet, output, allow_invalid_output=True
        )
    except (OSError, ValueError) as error:
        forensics = evaluator_runtime_forensics(
            kind, identity, attempt, source_packet, output, error
        )
        evidence = (
            f"{evidence} Runtime/packet verification failed: "
            f"{forensics['verification_error']}"
        )
    destination = SCORING / "invalid" / phase / identity / str(attempt)
    root = output.parent
    if forensics is None:
        entries = snapshot_path(output, destination / "raw-output")
        write_once(destination / "raw-output-manifest.json", json_dump(entries))
    else:
        entries = snapshot_path(root, destination / "raw-runtime")
        write_once(destination / "raw-runtime-manifest.json", json_dump(entries))
        source_entries = snapshot_path(
            source_packet, destination / "source-packet-at-verification"
        )
        write_once(
            destination / "source-packet-at-verification-manifest.json",
            json_dump(source_entries),
        )
    if forensics is not None:
        write_once(destination / "runtime-forensics.json", json_dump(forensics))
    attestation = {
        "schema_version": 1,
        "phase": phase,
        "identity": identity,
        "attempt": attempt,
        "agent_id": agent_id,
        "evidence": evidence,
        "disposition": "INVALID_NONRERUNNABLE_EVALUATOR_OUTPUT",
        "recorded_utc": utc_now(),
    }
    write_once(destination / "attestation.json", json_dump(attestation))
    make_read_only(destination)
    append_event(
        phase,
        "invalid_output_preserved",
        attempt=attempt,
        agent_id=agent_id,
        digest=byte_tree_digest(destination),
        details={"kind": kind, "identity": identity},
    )
    write_once(invalid_marker, json_dump(attestation))
    invalid_marker.chmod(0o444)
    append_event(
        phase,
        "evaluator_returned",
        attempt=attempt,
        agent_id=agent_id,
        details={"kind": kind, "identity": identity, "api_state": "INVALID_OUTPUT"},
    )
    append_event(
        phase,
        "run_invalidated",
        attempt=attempt,
        agent_id=agent_id,
        digest=sha256_file(invalid_marker),
        details={"identity": identity, "evidence": evidence},
    )
    print(invalid_marker)


def preserve_failed_evaluator_attempt(
    phase: str,
    identity: str,
    attempt: int,
    output: Path,
    agent_id: str,
    disposition: str,
    evidence: str,
) -> None:
    if disposition not in INFRA_FAILURE_CODES:
        raise ValueError(f"non-infrastructure evaluator disposition: {disposition}")
    if not evidence.strip():
        raise ValueError("evaluator infrastructure failure requires nonempty evidence")
    kind = "scorer" if phase == "scoring" else "adjudicator"
    assert_evaluator_started(kind, identity, attempt, agent_id)
    if kind == "scorer":
        mode, scorer = identity.split("-", 1)
        source_packet = SCORING / "packets" / mode / scorer
    else:
        source_packet = SCORING / "adjudication-packets" / identity
    verify_evaluator_runtime(
        kind, identity, attempt, source_packet, output, allow_invalid_output=True
    )
    destination = SCORING / "evaluator-attempts" / phase / identity / str(attempt)
    entries = snapshot_path(output, destination / "raw-output")
    write_once(destination / "raw-output-manifest.json", json_dump(entries))
    attestation = {
        "schema_version": 1,
        "phase": phase,
        "kind": kind,
        "identity": identity,
        "attempt": attempt,
        "agent_id": agent_id,
        "evidence": evidence,
        "disposition": disposition,
        "recorded_utc": utc_now(),
    }
    write_once(destination / "attestation.json", json_dump(attestation))
    make_read_only(destination)
    append_event(
        phase,
        "evaluator_attempt_preserved",
        attempt=attempt,
        agent_id=agent_id,
        digest=byte_tree_digest(destination),
        details={"kind": kind, "identity": identity, "disposition": disposition},
    )
    append_event(
        phase,
        "evaluator_returned",
        attempt=attempt,
        agent_id=agent_id,
        details={"kind": kind, "identity": identity, "api_state": "INFRASTRUCTURE_FAILURE"},
    )
    append_event(
        phase,
        "evaluator_infrastructure_failure",
        attempt=attempt,
        agent_id=agent_id,
        details={
            "kind": kind,
            "identity": identity,
            "disposition": disposition,
            "evidence": evidence,
        },
    )
    print(json_dump(attestation), end="")


def decision_lookup(value: dict[str, Any]) -> dict[tuple[str, str], dict[str, Any]]:
    return {(item["label"], item["field"]): item for item in value.get("decisions", [])}


def merge_final(mode: str) -> None:
    scores = {scorer: load_preserved_score(mode, scorer) for scorer in SCORERS}
    disagreement_path = SCORING / "disagreements" / f"{mode}.json"
    if sha256_file(disagreement_path) != preserved_digest(
        "disagreements_materialized", mode=mode
    ):
        raise ValueError(f"disagreements changed after preservation: {mode}")
    disagreements = json.loads(disagreement_path.read_text())
    if disagreements["cells"]:
        adjudication = json.loads((SCORING / "adjudications" / f"{mode}.json").read_text())
        expected_adjudication = preserved_digest("adjudication_preserved", mode=mode)
        if sha256_file(SCORING / "adjudications" / f"{mode}.json") != expected_adjudication:
            raise ValueError(f"adjudication changed after preservation: {mode}")
        validate_adjudication(adjudication, mode)
        decisions = decision_lookup(adjudication)
    else:
        decisions = {}
    by_scorer = {scorer: report_by_label(score) for scorer, score in scores.items()}
    final_reports: list[dict[str, Any]] = []
    confirmed_novel: list[dict[str, Any]] = []
    for label in LABELS:
        first = by_scorer["s1"][label]
        second = by_scorer["s2"][label]
        atoms: dict[str, str] = {}
        atoms1 = {atom["id"]: atom for atom in first["atoms"]}
        atoms2 = {atom["id"]: atom for atom in second["atoms"]}
        for atom in atom_ids(mode):
            if atoms1[atom]["decision"] == atoms2[atom]["decision"]:
                atoms[atom] = atoms1[atom]["decision"]
            else:
                atoms[atom] = decisions[(label, f"atom:{atom}")]["decision"]
        final_hard: list[str] = []
        for identifier in hard_error_ids(mode):
            present = [any(item["id"] == identifier for item in report["hard_errors"]) for report in (first, second)]
            if present[0] == present[1]:
                chosen = present[0]
            else:
                chosen = decisions[(label, f"hard_error:{identifier}")]["decision"] == "PRESENT"
            if chosen:
                final_hard.append(identifier)
        flags: dict[str, bool] = {}
        for field in ("proposal_laundering", "tcb_authority_defect", "visible_scope_defect"):
            present = [first[field]["present"], second[field]["present"]]
            if present[0] == present[1]:
                flags[field] = present[0]
            else:
                flags[field] = decisions[(label, field)]["decision"] == "PRESENT"
        final_reports.append({"label": label, "atoms": atoms, "hard_errors": final_hard, **flags})
        for scorer, report in (("s1", first), ("s2", second)):
            for finding in report["novel_findings"]:
                field = f"novel:{scorer}:{finding['id']}"
                if decisions[(label, field)]["decision"] == "PRESENT":
                    confirmed_novel.append({"label": label, "field": field, "evidence": decisions[(label, field)]["evidence"]})
    value = {"schema_version": 1, "mode": mode, "reports": final_reports, "confirmed_novel_findings": confirmed_novel}
    destination = SCORING / "final" / f"{mode}.json"
    write_once(destination, json_dump(value))
    destination.chmod(0o444)
    append_event("adjudication", "final_blind_score_locked", digest=sha256_file(destination), details={"mode": mode})
    print(destination)


def aggregate() -> None:
    schedule = load_schedule()
    conditions = load_condition_map()
    targets = load_target_map()
    blind = load_blind_map()
    index = load_index(require_collection_lock=True)
    counts: dict[str, dict[str, dict[str, int]]] = {}
    defects: dict[str, dict[str, list[dict[str, Any]]]] = {}
    failures: list[dict[str, Any]] = []
    novel: list[dict[str, Any]] = []
    final_digests: dict[str, str] = {}
    for mode in MODES:
        path = SCORING / "final" / f"{mode}.json"
        expected_final = preserved_digest("final_blind_score_locked", mode=mode)
        if sha256_file(path) != expected_final:
            raise ValueError(f"final blind score changed after lock: {mode}")
        value = json.loads(path.read_text())
        final_digests[mode] = sha256_file(path)
        reports = {report["label"]: report for report in value["reports"]}
        if tuple(sorted(reports)) != LABELS:
            raise ValueError(f"{mode} final labels incomplete")
        counts[mode] = {role: {atom: 0 for atom in atom_ids(mode)} for role in prepare.CONDITIONS}
        defects[mode] = {role: [] for role in prepare.CONDITIONS}
        for label, run_id in blind[mode].items():
            row = schedule[run_id]
            if targets[row["target_label"]]["mode"] != mode:
                raise ValueError("unblinding mode mismatch")
            role = conditions[row["condition_label"]]["role"]
            report = reports[label]
            for atom, decision in report["atoms"].items():
                if decision == "PASS":
                    counts[mode][role][atom] += 1
                else:
                    failures.append({"mode": mode, "role": role, "run_id": run_id, "label": label, "atom": atom})
            over_budget = index[run_id]["word_count"] > index[run_id]["word_cap"]
            flags = {
                "hard_errors": report["hard_errors"],
                "proposal_laundering": report["proposal_laundering"],
                "tcb_authority_defect": report["tcb_authority_defect"],
                "visible_scope_defect": report["visible_scope_defect"],
                "operational_scope_deviation": index[run_id]["operational_scope_deviation"],
                "word_budget_defect": over_budget,
                "semantic_noncompletion": index[run_id]["semantic_noncompletion"],
            }
            if flags["hard_errors"] or any(
                flags[name]
                for name in (
                    "proposal_laundering",
                    "tcb_authority_defect",
                    "visible_scope_defect",
                    "operational_scope_deviation",
                    "word_budget_defect",
                    "semantic_noncompletion",
                )
            ):
                defects[mode][role].append({"run_id": run_id, "label": label, **flags})
        for finding in value["confirmed_novel_findings"]:
            novel.append({"mode": mode, **finding})
    v3_failures = [failure for failure in failures if failure["role"] == "v3"]
    v3_defects = [item for mode in MODES for item in defects[mode]["v3"]]
    gate = {
        "all_v3_atoms_5_of_5": not v3_failures,
        "zero_v3_hard_errors": not any(item["hard_errors"] for item in v3_defects),
        "zero_v3_proposal_laundering": not any(item["proposal_laundering"] for item in v3_defects),
        "zero_v3_tcb_authority_defects": not any(item["tcb_authority_defect"] for item in v3_defects),
        "zero_v3_semantic_noncompletion": not any(
            item["semantic_noncompletion"] for item in v3_defects
        ),
        "zero_v3_scope_budget_defects": not any(
            item["visible_scope_defect"]
            or item["operational_scope_deviation"]
            or item["word_budget_defect"]
            for item in v3_defects
        ),
    }
    gate["overall"] = all(gate.values())
    diagnostic_comparisons: list[dict[str, Any]] = []
    for mode in MODES:
        for atom in atom_ids(mode):
            v3_count = counts[mode]["v3"][atom]
            v2_count = counts[mode]["v2"][atom]
            if v3_count < v2_count:
                classification = "V3_BELOW_V2"
            elif v3_count == 5 and v2_count < 5:
                classification = "TARGETED_LIFT_EVIDENCE"
            elif v3_count == 5 and v2_count == 5:
                classification = "CEILING_REPLICATION"
            elif v3_count > v2_count:
                classification = "V3_HIGHER_BUT_CONFIRMATION_FAILED"
            else:
                classification = "MATCHED_BELOW_CEILING"
            diagnostic_comparisons.append(
                {
                    "mode": mode,
                    "atom": atom,
                    "v3_passes": v3_count,
                    "v2_passes": v2_count,
                    "classification": classification,
                }
            )
    result = {
        "schema_version": 1,
        "unblinded_utc": utc_now(),
        "condition_map": {label: row["role"] for label, row in conditions.items()},
        "final_score_sha256": final_digests,
        "counts": counts,
        "defects": defects,
        "failed_atom_cells": failures,
        "confirmed_novel_findings": novel,
        "diagnostic_comparison": {
            "any_v3_below_v2": any(
                item["classification"] == "V3_BELOW_V2"
                for item in diagnostic_comparisons
            ),
            "causal_claim": False,
            "reason": "The coherent V3 and V2 packages differ in more than one isolated instruction.",
            "atoms": diagnostic_comparisons,
        },
        "v3_gate": gate,
    }
    RESULTS.mkdir(parents=True, exist_ok=True)
    write_once(RUN / "unblinding.json", json_dump({"schema_version": 1, "unblinded_utc": result["unblinded_utc"], "condition_map": result["condition_map"], "final_score_sha256": final_digests}))
    write_once(RESULTS / "aggregate.json", json_dump(result))
    lines = [
        "# V3 Targeted Confirmation Results",
        "",
        f"**Primary V3 gate: {'PASS' if gate['overall'] else 'FAIL'}.**",
        "",
        "Each atom cell is a pass count out of five. V3 is the confirmatory candidate; V2 is diagnostic.",
        "",
        "| Mode | Condition | Atom pass counts | Defective reports |",
        "|---|---|---|---:|",
    ]
    for mode in MODES:
        for role in ("v3", "v2"):
            rendered = "; ".join(f"{atom} {count}/5" for atom, count in counts[mode][role].items())
            lines.append(f"| {mode} | {role.upper()} | {rendered} | {len(defects[mode][role])} |")
    lines.extend(
        [
            "",
            "## Diagnostic comparison",
            "",
            f"Any V3 atom below matched V2: {'YES' if result['diagnostic_comparison']['any_v3_below_v2'] else 'NO'}.",
            "",
            "`TARGETED_LIFT_EVIDENCE` means V3 passed 5/5 while matched V2 was lower. "
            "`CEILING_REPLICATION` means both passed 5/5. These coherent packages differ "
            "in more than one isolated instruction, so no classification is causal proof.",
            "",
            "| Mode | Atom | V3 | V2 | Classification |",
            "|---|---|---:|---:|---|",
        ]
    )
    for item in diagnostic_comparisons:
        lines.append(
            f"| {item['mode']} | {item['atom']} | {item['v3_passes']}/5 | "
            f"{item['v2_passes']}/5 | {item['classification']} |"
        )
    lines.extend(["", "## Primary gates", "", "| Gate | Result |", "|---|---|"])
    for name, passed in gate.items():
        if name != "overall":
            lines.append(f"| {name.replace('_', ' ')} | {'PASS' if passed else 'FAIL'} |")
    lines.extend(["", "## Integrity limitations", "", "Filesystem and URL isolation were procedural on a shared host. Exact hosted model-build and sampling-seed metadata were unavailable. Results are source-review capability observations under those constraints.", ""])
    write_once(RESULTS / "summary.md", "\n".join(lines))
    append_event("unblinding", "conditions_revealed", digest=sha256_file(RUN / "unblinding.json"), details={})
    append_event(
        "result",
        "aggregate_written",
        digest=sha256_file(RESULTS / "aggregate.json"),
        details={
            "v3_gate": gate["overall"],
            "summary_sha256": sha256_file(RESULTS / "summary.md"),
        },
    )
    print(RESULTS / "summary.md")


def record_freeze_lock() -> None:
    if any(event["event"] == "freeze_locked" for event in event_records()):
        raise ValueError("freeze lock was already recorded")
    append_event(
        "freeze",
        "freeze_locked",
        digest=sha256_file(FILE_MANIFEST),
        details={"lock_sha256": sha256_file(LOCK)},
    )
    print("freeze lock recorded")


def assert_freeze_locked() -> None:
    matches = [event for event in event_records() if event["event"] == "freeze_locked"]
    if len(matches) != 1:
        raise ValueError("evaluation operations require exactly one freeze-lock event")
    event = matches[0]
    if (
        event.get("sha256") != sha256_file(FILE_MANIFEST)
        or event.get("details", {}).get("lock_sha256") != sha256_file(LOCK)
    ):
        raise ValueError("freeze-lock event does not bind the current lock")


def main() -> None:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    verify = sub.add_parser("verify-static")
    verify.add_argument("--locked", action="store_true")
    sub.add_parser("self-test")
    sub.add_parser("write-file-manifest")
    sub.add_parser("record-freeze-lock")
    prepare_cell_parser = sub.add_parser("prepare-cell")
    prepare_cell_parser.add_argument("run_id")
    prepare_cell_parser.add_argument("runtime", type=Path)
    report_prompt = sub.add_parser("report-prompt")
    report_prompt.add_argument("run_id")
    report_prompt.add_argument("runtime", type=Path)
    record_report_parser = sub.add_parser("record-report")
    record_report_parser.add_argument("run_id")
    record_report_parser.add_argument("attempt", type=positive_int)
    record_report_parser.add_argument("runtime", type=Path)
    record_report_parser.add_argument("agent_id")
    record_report_parser.add_argument("--scope-deviation", action="store_true")
    record_report_parser.add_argument(
        "--scope-evidence", default="No known operational source-scope deviation."
    )
    failed_report_parser = sub.add_parser("record-failed-report")
    failed_report_parser.add_argument("run_id")
    failed_report_parser.add_argument("attempt", type=positive_int)
    failed_report_parser.add_argument("runtime", type=Path)
    failed_report_parser.add_argument("agent_id")
    failed_report_parser.add_argument(
        "disposition", choices=sorted(INFRA_FAILURE_CODES | TERMINAL_REPORT_FAILURE_CODES)
    )
    failed_report_parser.add_argument("evidence")
    failed_report_parser.add_argument("--scope-deviation", action="store_true")
    agent_start_parser = sub.add_parser("agent-start")
    agent_start_parser.add_argument("run_id")
    agent_start_parser.add_argument("attempt", type=positive_int)
    agent_start_parser.add_argument("agent_id")
    prelaunch_parser = sub.add_parser("record-prelaunch-failure")
    prelaunch_parser.add_argument("run_id")
    prelaunch_parser.add_argument("evidence")
    reminder_parser = sub.add_parser("reminder-text")
    reminder_parser.add_argument("run_id")
    reminder_parser.add_argument("attempt", type=positive_int)
    reminder_parser.add_argument("agent_id")
    sub.add_parser("build-score-packets")
    scorer_prompt = sub.add_parser("scorer-prompt")
    scorer_prompt.add_argument("mode", choices=MODES)
    scorer_prompt.add_argument("scorer", choices=SCORERS)
    scorer_prompt.add_argument("attempt", type=positive_int)
    scorer_prompt.add_argument("output", type=Path)
    record_score_parser = sub.add_parser("record-score")
    record_score_parser.add_argument("mode", choices=MODES)
    record_score_parser.add_argument("scorer", choices=SCORERS)
    record_score_parser.add_argument("attempt", type=positive_int)
    record_score_parser.add_argument("output", type=Path)
    record_score_parser.add_argument("agent_id")
    invalid_score_parser = sub.add_parser("record-invalid-score")
    invalid_score_parser.add_argument("mode", choices=MODES)
    invalid_score_parser.add_argument("scorer", choices=SCORERS)
    invalid_score_parser.add_argument("attempt", type=positive_int)
    invalid_score_parser.add_argument("output", type=Path)
    invalid_score_parser.add_argument("agent_id")
    invalid_score_parser.add_argument("evidence")
    disagreements_parser = sub.add_parser("build-disagreements")
    disagreements_parser.add_argument("mode", choices=MODES)
    adjudication_packet = sub.add_parser("build-adjudication-packet")
    adjudication_packet.add_argument("mode", choices=MODES)
    adjudicator_prompt = sub.add_parser("adjudicator-prompt")
    adjudicator_prompt.add_argument("mode", choices=MODES)
    adjudicator_prompt.add_argument("attempt", type=positive_int)
    adjudicator_prompt.add_argument("output", type=Path)
    record_adjudication_parser = sub.add_parser("record-adjudication")
    record_adjudication_parser.add_argument("mode", choices=MODES)
    record_adjudication_parser.add_argument("attempt", type=positive_int)
    record_adjudication_parser.add_argument("output", type=Path)
    record_adjudication_parser.add_argument("agent_id")
    invalid_adjudication_parser = sub.add_parser("record-invalid-adjudication")
    invalid_adjudication_parser.add_argument("mode", choices=MODES)
    invalid_adjudication_parser.add_argument("attempt", type=positive_int)
    invalid_adjudication_parser.add_argument("output", type=Path)
    invalid_adjudication_parser.add_argument("agent_id")
    invalid_adjudication_parser.add_argument("evidence")
    evaluator_start_parser = sub.add_parser("evaluator-start")
    evaluator_start_parser.add_argument("kind", choices=("scorer", "adjudicator"))
    evaluator_start_parser.add_argument("identity")
    evaluator_start_parser.add_argument("attempt", type=positive_int)
    evaluator_start_parser.add_argument("agent_id")
    evaluator_prelaunch = sub.add_parser("record-evaluator-prelaunch-failure")
    evaluator_prelaunch.add_argument("kind", choices=("scorer", "adjudicator"))
    evaluator_prelaunch.add_argument("identity")
    evaluator_prelaunch.add_argument("attempt", type=positive_int)
    evaluator_prelaunch.add_argument("output", type=Path)
    evaluator_prelaunch.add_argument("evidence")
    failed_evaluator = sub.add_parser("record-failed-evaluator")
    failed_evaluator.add_argument("kind", choices=("scorer", "adjudicator"))
    failed_evaluator.add_argument("identity")
    failed_evaluator.add_argument("attempt", type=positive_int)
    failed_evaluator.add_argument("output", type=Path)
    failed_evaluator.add_argument("agent_id")
    failed_evaluator.add_argument("disposition", choices=sorted(INFRA_FAILURE_CODES))
    failed_evaluator.add_argument("evidence")
    merge_parser = sub.add_parser("merge-final")
    merge_parser.add_argument("mode", choices=MODES)
    sub.add_parser("aggregate")
    args = parser.parse_args()

    operational_commands = {
        "record-freeze-lock",
        "prepare-cell",
        "report-prompt",
        "agent-start",
        "record-prelaunch-failure",
        "reminder-text",
        "record-report",
        "record-failed-report",
        "build-score-packets",
        "scorer-prompt",
        "record-score",
        "record-invalid-score",
        "build-disagreements",
        "build-adjudication-packet",
        "adjudicator-prompt",
        "record-adjudication",
        "record-invalid-adjudication",
        "evaluator-start",
        "record-evaluator-prelaunch-failure",
        "record-failed-evaluator",
        "merge-final",
        "aggregate",
    }
    operation_lock_handle = None
    if args.command in operational_commands:
        operation_lock_handle = acquire_operation_lock()
        terminal_invalid_event = any(
            event["event"] in {"invalid_output_preserved", "run_invalidated"}
            for event in event_records()
        )
        invalid_marker = RUN / "INVALID.json"
        if invalid_marker.exists() or invalid_marker.is_symlink() or terminal_invalid_event:
            raise SystemExit("run is INVALID; no further evaluation command is permitted")
        validate_static(require_lock=True, announce=False)
        if args.command == "record-freeze-lock":
            if any(event["event"] == "freeze_locked" for event in event_records()):
                raise SystemExit("freeze lock was already recorded")
        else:
            assert_freeze_locked()

    if args.command == "verify-static":
        validate_static(args.locked)
    elif args.command == "self-test":
        self_test()
    elif args.command == "write-file-manifest":
        if FILE_MANIFEST.exists():
            raise FileExistsError(FILE_MANIFEST)
        write_once(FILE_MANIFEST, render_file_manifest())
        print(f"{FILE_MANIFEST.relative_to(RUN)} {sha256_file(FILE_MANIFEST)}")
    elif args.command == "record-freeze-lock":
        record_freeze_lock()
    elif args.command == "prepare-cell":
        prepare_cell(args.run_id, args.runtime)
    elif args.command == "report-prompt":
        verify_runtime(args.run_id, args.runtime)
        print(render_report_prompt(args.run_id, args.runtime), end="")
    elif args.command == "record-report":
        record_report(
            args.run_id,
            args.attempt,
            args.runtime,
            args.agent_id,
            args.scope_deviation,
            args.scope_evidence,
        )
    elif args.command == "record-failed-report":
        preserve_failed_report_attempt(
            args.run_id,
            args.attempt,
            args.runtime,
            args.agent_id,
            args.disposition,
            args.evidence,
            args.scope_deviation,
        )
    elif args.command == "agent-start":
        record_agent_start(args.run_id, args.attempt, args.agent_id)
    elif args.command == "record-prelaunch-failure":
        record_prelaunch_failure(args.run_id, args.evidence)
    elif args.command == "reminder-text":
        record_reminder(args.run_id, args.attempt, args.agent_id)
        print(report_reminder_text(), end="")
    elif args.command == "build-score-packets":
        build_score_packets()
    elif args.command == "scorer-prompt":
        source_packet = SCORING / "packets" / args.mode / args.scorer
        verify_score_packet(args.mode, args.scorer)
        packet = prepare_evaluator_runtime(
            "scorer",
            f"{args.mode}-{args.scorer}",
            args.attempt,
            source_packet,
            args.output,
        )
        print(
            render_packet_prompt("scorer.md", packet, args.output, SCORER_ID=args.scorer),
            end="",
        )
    elif args.command == "record-score":
        record_score(args.mode, args.scorer, args.attempt, args.output, args.agent_id)
    elif args.command == "record-invalid-score":
        record_invalid_evaluator(
            "scoring",
            f"{args.mode}-{args.scorer}",
            args.attempt,
            args.output,
            args.agent_id,
            args.evidence,
        )
    elif args.command == "build-disagreements":
        build_disagreements(args.mode)
    elif args.command == "build-adjudication-packet":
        build_adjudication_packet(args.mode)
    elif args.command == "adjudicator-prompt":
        source_packet = SCORING / "adjudication-packets" / args.mode
        verify_adjudication_packet(args.mode)
        packet = prepare_evaluator_runtime(
            "adjudicator", args.mode, args.attempt, source_packet, args.output
        )
        print(render_packet_prompt("adjudicator.md", packet, args.output), end="")
    elif args.command == "record-adjudication":
        record_adjudication(args.mode, args.attempt, args.output, args.agent_id)
    elif args.command == "record-invalid-adjudication":
        record_invalid_evaluator(
            "adjudication",
            args.mode,
            args.attempt,
            args.output,
            args.agent_id,
            args.evidence,
        )
    elif args.command == "evaluator-start":
        record_evaluator_start(args.kind, args.identity, args.attempt, args.agent_id)
    elif args.command == "record-evaluator-prelaunch-failure":
        record_evaluator_prelaunch_failure(
            args.kind, args.identity, args.attempt, args.output, args.evidence
        )
    elif args.command == "record-failed-evaluator":
        preserve_failed_evaluator_attempt(
            "scoring" if args.kind == "scorer" else "adjudication",
            args.identity,
            args.attempt,
            args.output,
            args.agent_id,
            args.disposition,
            args.evidence,
        )
    elif args.command == "merge-final":
        merge_final(args.mode)
    elif args.command == "aggregate":
        aggregate()


if __name__ == "__main__":
    main()
