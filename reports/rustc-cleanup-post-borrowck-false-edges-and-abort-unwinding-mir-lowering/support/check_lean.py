#!/usr/bin/env python3
"""Kernel-check `CleanupPostBorrowckAndAbortCalls.lean` and audit what it declares.

Steps (all results are measured by this run and written to a JSON receipt):

1. scan the formalization source text for forbidden tokens that must not occur anywhere in it;
2. compile the module with a synchronous elaborator, strict kernel checker, and warnings-as-errors
   (`lean -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true -o <tmp>/CleanupPostBorrowckAndAbortCalls.olean`);
3. run `CleanupPostBorrowckAudit.lean` against the compiled module: walk every constant declared in
   the module, reject axioms, `opaque` constants, non-`safe` definitions, and `_unsafe_rec` helpers,
   and reject any theorem whose proof uses an axiom other than `propext` and `Quot.sound`;
4. record source hashes, sizes, declaration counts, wall-clock time, and peak resident memory.

Usage:

    python3 support/check_lean.py --lean lean --out support/lean_check_receipt.json

`--wrap` prepends a launcher command (used when hosts run compilers under resource limits); launcher
arguments are never written to the JSON receipt. The script exits non-zero if any step fails.
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
MODULE = "CleanupPostBorrowckAndAbortCalls"
AUDIT = "CleanupPostBorrowckAudit"

# Whole-word, case-insensitive. None of these may appear anywhere in the module source,
# comments included.
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
    """Internal helper mode: run `cmd`, report its wall-clock time and peak resident memory."""
    import resource
    import time

    start = time.perf_counter()
    proc = subprocess.run(cmd)
    wall = time.perf_counter() - start
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    print("MEASURE " + json.dumps({"wall_seconds": round(wall, 3), "peak_rss_kb": rss}), file=sys.stderr)
    return proc.returncode


def timed(cmd: list[str], env: dict[str, str], wrap: list[str], cwd: Path):
    """Run `cmd` under `wrap`; return (exit code, stdout, stderr, wall seconds, peak RSS kB)."""
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


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:2] == ["--measure", "--"]:
        return measure_child(argv[2:])

    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--wrap", default="", help="launcher command placed in front of every compiler call")
    ap.add_argument("--out", default=str(HERE / "lean_check_receipt.json"))
    args = ap.parse_args(argv)
    wrap = shlex.split(args.wrap)

    src = HERE / f"{MODULE}.lean"
    audit = HERE / f"{AUDIT}.lean"
    text = src.read_text(encoding="utf-8")
    tokens = scan_tokens(text)
    lines = text.splitlines()

    ver = subprocess.run([args.lean, "--version"], stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    version_line = ver.stdout.decode("utf-8", "replace").strip()

    receipt: dict[str, object] = {
        "schema": "lean-check-receipt/1",
        "generated_on": datetime.date.today().isoformat(),
        "lean_version": version_line,
        "module": f"support/{MODULE}.lean",
        "audit_module": f"support/{AUDIT}.lean",
        "source_sha256": hashlib.sha256(src.read_bytes()).hexdigest(),
        "source_bytes": src.stat().st_size,
        "source_lines": len(lines),
        "source_theorem_keywords": sum(1 for l in lines if re.match(r"\s*(?:private\s+)?theorem\s", l)),
        "source_public_theorem_keywords": sum(1 for l in lines if re.match(r"theorem\s", l)),
        "source_def_keywords": sum(1 for l in lines if re.match(r"\s*(?:private\s+)?(?:noncomputable\s+)?def\s", l)),
        "source_inductive_keywords": sum(1 for l in lines if re.match(r"\s*(?:private\s+)?(?:inductive|structure)\s", l)),
        "imports": [l.split()[1] for l in lines if l.startswith("import ")],
        "forbidden_token_counts": tokens,
        "compile_flags": ["-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"],
    }
    ok = all(v == 0 for v in tokens.values())

    with tempfile.TemporaryDirectory(prefix="mir_cleanup_lean_") as tmp:
        olean = Path(tmp) / f"{MODULE}.olean"
        env = dict(os.environ)
        rc, out, err, wall, rss = timed(
            [
                args.lean,
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
                [
                    args.lean,
                    "-DElab.async=false",
                    "-Ddebug.skipKernelTC=false",
                    "-DwarningAsError=true",
                    str(audit),
                ],
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
                axioms_printed[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
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
            receipt["compile"]["first_diagnostics"] = diagnostics[:15]

    receipt["passed"] = bool(ok)
    Path(args.out).write_text(json.dumps(receipt, indent=1, sort_keys=True) + "\n", encoding="utf-8")
    print(
        json.dumps(
            {
                k: receipt[k]
                for k in ("lean_version", "source_sha256", "forbidden_token_counts", "compile", "passed")
            },
            indent=1,
        )
    )
    if "audit" in receipt:
        print(json.dumps(receipt["audit"], indent=1))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
