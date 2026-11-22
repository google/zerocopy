#!/usr/bin/env python3
"""Kernel-check `PackedDropsCheckPackedRefAndElaborateDropsSoundness.lean` and audit purity.

Steps:
1. Scan source text for forbidden tokens (`sorry`, `admit`, `omega`, `bv_decide`,
   `native_decide`, `partial`, `unsafe`, `axiom`, `opaque`, `implemented_by`, `extern`,
   `Classical`, `_unsafe_rec`) — whole-word, case-insensitive, including comments.
2. Compile with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.
3. Run `AuditPackedDropsLean.lean` against the compiled `.olean` to inspect every constant
   in the module's environment (`0` `_unsafe_rec`, `0` non-`.safe` defs, `0` disallowed axioms).
4. Write a machine-readable JSON receipt.

Usage:
    python3 support/check_lean.py --lean lean --out support/lean_check_receipt.json
"""

from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
MODULE = "PackedDropsCheckPackedRefAndElaborateDropsSoundness"
AUDIT = "AuditPackedDropsLean"

FORBIDDEN_TOKENS = [
    "sorry",
    "admit",
    "omega",
    "bv_decide",
    "native_decide",
    "partial",
    "unsafe",
    "axiom",
    "opaque",
    "implemented_by",
    "extern",
    "Classical",
    "_unsafe_rec",
]


def scan_tokens(text: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for tok in FORBIDDEN_TOKENS:
        counts[tok] = len(
            re.findall(r"(?<![A-Za-z0-9_])" + re.escape(tok) + r"(?![A-Za-z0-9_])", text, flags=re.I)
        )
    return counts


def measure_child(cmd: list[str]) -> int:
    import resource
    import time

    start = time.perf_counter()
    proc = subprocess.run(cmd)
    wall = time.perf_counter() - start
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    print("MEASURE " + json.dumps({"wall_seconds": round(wall, 3), "peak_rss_kb": rss}), file=sys.stderr)
    return proc.returncode


def timed(cmd: list[str], env: dict[str, str], wrap: list[str], cwd: Path):
    full = list(wrap) + [sys.executable, str(Path(__file__).resolve()), "--measure", "--"] + cmd
    proc = subprocess.run(full, env=env, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    out = proc.stdout.decode("utf-8", "replace")
    err = proc.stderr.decode("utf-8", "replace")
    wall = rss = None
    m = re.search(r"MEASURE (\{.*\})", err)
    if m:
        data = json.loads(m.group(1))
        wall, rss = data["wall_seconds"], data["peak_rss_kb"]
    return proc.returncode, out, err, wall, rss


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:2] == ["--measure", "--"]:
        return measure_child(argv[2:])

    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--wrap", default="", help="Optional launcher wrapper (e.g. anneal-lean-run)")
    ap.add_argument("--out", default=str(HERE / "lean_check_receipt.json"))
    args = ap.parse_args(argv)
    wrap = shlex.split(args.wrap)

    src = HERE / f"{MODULE}.lean"
    audit = HERE / f"{AUDIT}.lean"
    text = src.read_text()
    tokens = scan_tokens(text)
    lines = text.splitlines()

    ver = subprocess.run([args.lean, "--version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    version_line = ver.stdout.decode().strip()

    receipt = {
        "schema": "lean-check-receipt/1",
        "generated_on": datetime.date.today().isoformat(),
        "lean_version": version_line,
        "module": f"support/{MODULE}.lean",
        "source_sha256": hashlib.sha256(src.read_bytes()).hexdigest(),
        "source_bytes": src.stat().st_size,
        "source_lines": len(lines),
        "source_theorem_keywords": sum(1 for l in lines if re.match(r"\s*theorem\s", l)),
        "source_def_keywords": sum(1 for l in lines if re.match(r"\s*(noncomputable\s+)?def\s", l)),
        "source_inductive_keywords": sum(1 for l in lines if re.match(r"\s*(inductive|structure)\s", l)),
        "forbidden_token_counts": tokens,
        "compile_flags": ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"],
    }
    ok = all(v == 0 for v in tokens.values())

    with tempfile.TemporaryDirectory(prefix="packed_drops_lean_") as tmp:
        olean = Path(tmp) / f"{MODULE}.olean"
        env = dict(os.environ)
        rc, out, err, wall, rss = timed(
            [
                args.lean,
                "-M2048",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-DwarningAsError=true",
                "-o",
                str(olean),
                str(src),
            ],
            env,
            wrap,
            HERE,
        )
        diagnostics = [l for l in (out + err).splitlines() if re.search(r": (error|warning)", l)]
        receipt["compile"] = {
            "exit_code": rc,
            "errors": sum(1 for l in diagnostics if ": error" in l),
            "warnings": sum(1 for l in diagnostics if ": warning" in l),
            "wall_seconds": wall,
            "peak_rss_kb": rss,
            "olean_bytes": olean.stat().st_size if olean.exists() else None,
        }
        ok = ok and rc == 0 and receipt["compile"]["errors"] == 0 and receipt["compile"]["warnings"] == 0

        if rc == 0:
            env2 = dict(os.environ, LEAN_PATH=tmp)
            rc2, out2, err2, wall2, rss2 = timed(
                [args.lean, "-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", str(audit)],
                env2,
                wrap,
                HERE,
            )
            audit_json = None
            for line in (out2 + err2).splitlines():
                m = re.search(r"AUDIT (\{.*\})", line)
                if m:
                    audit_json = json.loads(m.group(1))
            axioms_printed: dict[str, list[str]] = {}
            for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out2 + err2):
                axioms_printed[m.group(1)] = [a.strip() for a in m.group(2).split(",")]
            for m in re.finditer(r"'([^']+)' does not depend on any axioms", out2 + err2):
                axioms_printed[m.group(1)] = []
            violation_lines = [
                line.strip()
                for line in (out2 + err2).splitlines()
                if re.match(
                    r"\s*(theorem .* depends on axiom|axiom:|opaque constant:|quot constant:|non-safe definition:|unsafe_rec helper:)",
                    line,
                )
            ]
            receipt["audit"] = {
                "exit_code": rc2,
                "summary": audit_json,
                "violation_lines": violation_lines,
                "print_axioms": axioms_printed,
                "wall_seconds": wall2,
                "peak_rss_kb": rss2,
            }
            ok = ok and rc2 == 0 and audit_json is not None and audit_json["violations"] == 0
        else:
            receipt["compile"]["first_diagnostics"] = diagnostics[:20]

    receipt["passed"] = bool(ok)
    Path(args.out).write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n")
    print(json.dumps(receipt, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
