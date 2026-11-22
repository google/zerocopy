#!/usr/bin/env python3
"""Standalone TLC 2.15 revalidation driver for TLA+, NDJSON, and Quint ITF probes.

Compiles flat NDJSON or Quint ITF JSON trace logs into a temporary pure-TLA+
`TraceData.tla` module so standard `tla2tools.jar` (without CommunityModules)
executes `T2Trace.tla` / `H1Trace.tla` directly via `tlc2.TLC`.

Usage:
  python3 run_tlc_probes.py --tla2tools /path/to/tla2tools.jar [--java /path/to/java] [--skip-full-t2]
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

HERE = Path(__file__).resolve().parent
TLA_IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")


def tla_escape_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def json_to_tla(val: Any) -> str:
    if isinstance(val, bool):
        return "TRUE" if val else "FALSE"
    if isinstance(val, int):
        return str(val)
    if isinstance(val, str):
        return tla_escape_str(val)
    if val is None:
        return '"NONE"'
    if isinstance(val, list):
        return "<< " + ", ".join(json_to_tla(x) for x in val) + " >>"
    if isinstance(val, dict):
        if set(val.keys()) == {"#bigint"}:
            raw = val["#bigint"]
            if not isinstance(raw, str) or not re.match(r"^-?[0-9]+$", raw):
                raise ValueError(f"Invalid ITF #bigint: {val!r}")
            return raw
        if set(val.keys()) == {"#set"}:
            return "{ " + ", ".join(json_to_tla(x) for x in val["#set"]) + " }"
        if set(val.keys()) == {"#tup"}:
            return "<< " + ", ".join(json_to_tla(x) for x in val["#tup"]) + " >>"
        if set(val.keys()) == {"#map"}:
            pairs = val["#map"]
            if not pairs:
                return "[ x \\in {} |-> 0 ]"
            return "(" + " @@ ".join(
                f"({json_to_tla(k)} :> {json_to_tla(v)})" for k, v in pairs
            ) + ")"
        if not val:
            return "[ x \\in {} |-> 0 ]"
        fields = []
        for k, v in val.items():
            if not isinstance(k, str) or not TLA_IDENT_RE.match(k):
                raise ValueError(f"Invalid TLA+ record field: {k!r}")
            fields.append(f"{k} |-> {json_to_tla(v)}")
        return "[ " + ", ".join(fields) + " ]"
    raise ValueError(f"Unsupported JSON value: {val!r}")


def parse_ndjson(path: Path) -> list[dict[str, Any]]:
    events: list[dict[str, Any]] = []
    for raw in path.read_text().splitlines():
        line = raw.strip()
        if not line:
            continue
        obj = json.loads(line)
        if "event" in obj:
            events.append(obj)
    return events


def parse_itf(path: Path) -> list[dict[str, Any]]:
    doc = json.loads(path.read_text())
    if doc.get("#meta", {}).get("format") != "ITF":
        raise ValueError(f"{path}: invalid ITF #meta.format")
    events: list[dict[str, Any]] = []
    for idx, st in enumerate(doc["states"]):
        if idx == 0:
            continue
        ev = dict(st.get("last_event") or st.get("event"))
        for k, v in st.items():
            if k not in ("#meta", "last_event", "event") and k not in ev:
                ev[k] = v
        events.append(ev)
    return events


def run_case(
    name: str,
    spec: str,
    cfg: str,
    java_bin: str,
    tla2tools: Path,
    ndjson: str | None = None,
    itf: str | None = None,
) -> dict[str, Any]:
    t0 = time.monotonic()
    with tempfile.TemporaryDirectory(prefix="tlc_probe_") as td:
        tmp = Path(td)
        for f in HERE.glob("*.tla"):
            shutil.copy2(f, tmp / f.name)
        for f in HERE.glob("*.cfg"):
            shutil.copy2(f, tmp / f.name)
        if ndjson or itf:
            evs = parse_ndjson(HERE / ndjson) if ndjson else parse_itf(HERE / itf)
            body = ",\n    ".join(json_to_tla(e) for e in evs)
            (tmp / "TraceData.tla").write_text(
                "------------------------------ MODULE TraceData ------------------------------\n"
                "EXTENDS Integers, Sequences, TLC\n\n"
                f"TraceLog == <<\n    {body}\n>>\n"
                "=============================================================================\n"
            )
        cmd = [
            java_bin,
            "-XX:+UseParallelGC",
            "-Xmx2g",
            "-cp",
            str(tla2tools),
            "tlc2.TLC",
            "-cleanup",
            "-workers",
            "1",
            "-metadir",
            str(tmp / "states"),
            "-config",
            cfg,
            spec,
        ]
        proc = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True)
    combined = proc.stdout + "\n" + proc.stderr
    m = re.search(r"(\d+) states generated,\s*(\d+) distinct states found", combined)
    return {
        "name": name,
        "exit_code": proc.returncode,
        "states_generated": int(m.group(1)) if m else None,
        "distinct_states": int(m.group(2)) if m else None,
        "wall_s": round(time.monotonic() - t0, 3),
    }


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tla2tools", type=Path, required=True)
    ap.add_argument("--java", default=shutil.which("java") or "java")
    ap.add_argument("--skip-full-t2", action="store_true")
    args = ap.parse_args()

    cases = [
        ("M5_vacuous_pass", "M5_ContradictoryAction.tla", "M5_ContradictoryAction.cfg", None, None, 0),
        ("MC_hunt_fsync_fail", "T2Spec.tla", "MC_hunt_fsync.cfg", None, None, 12),
        ("t2_valid_ndjson_pass", "T2Trace.tla", "T2Trace.cfg", "t2_valid.ndjson", None, 0),
        ("t2_valid_itf_pass", "T2Trace.tla", "T2Trace.cfg", None, "t2_valid.itf.json", 0),
        ("t2_m1_ndjson_fail", "T2Trace.tla", "T2Trace.cfg", "t2_m1_missing_fsync.ndjson", None, 11),
        ("t2_m1_itf_fail", "T2Trace.tla", "T2Trace.cfg", None, "t2_m1_missing_fsync.itf.json", 11),
        ("m6_lying_ndjson_blind_pass", "T2Trace.tla", "T2Trace.cfg", "m6_lying_trace.ndjson", None, 0),
        ("h1_spec_pass", "H1Spec.tla", "H1Spec.cfg", None, None, 0),
        ("h1_valid_ndjson_pass", "H1Trace.tla", "H1Trace.cfg", "h1_valid.ndjson", None, 0),
        ("h1_valid_itf_pass", "H1Trace.tla", "H1Trace.cfg", None, "h1_valid.itf.json", 0),
        ("h1_bug_ndjson_fail", "H1Trace.tla", "H1Trace.cfg", "h1_bug_stale_primary.ndjson", None, 11),
    ]
    if not args.skip_full_t2:
        cases.append(("t2_spec_full_pass", "T2Spec.tla", "T2Spec.cfg", None, None, 0))

    ok = True
    results = []
    for name, spec, cfg, ndj, itf, exp_rc in cases:
        res = run_case(name, spec, cfg, args.java, args.tla2tools.resolve(), ndj, itf)
        res["expected_exit_code"] = exp_rc
        res["matched"] = (res["exit_code"] == exp_rc)
        if not res["matched"]:
            ok = False
        results.append(res)
        print(json.dumps(res))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
