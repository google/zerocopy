#!/usr/bin/env python3
"""Kernel-check `ColdBlocksAndNoUnwindSoundness.lean` and audit its declarations.

Steps:
1. Scan source text for whole-word forbidden tokens (including comments).
2. Compile with `-M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`.
3. Run `ColdBlocksAndNoUnwindAudit.lean` against the compiled `.olean`.
4. Emit `lean_check_receipt.json` recording hashes, declaration counts, timing, and RSS.
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
MODULE = "ColdBlocksAndNoUnwindSoundness"
AUDIT = "ColdBlocksAndNoUnwindAudit"

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


def resolve_lean(requested: str) -> str:
    if requested != "lean":
        return requested
    toolchain = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
    if toolchain.is_file():
        return str(toolchain)
    return "lean"


def scan_tokens(text: str) -> dict[str, int]:
    counts = {}
    for tok in FORBIDDEN_TOKENS:
        counts[tok] = len(
            re.findall(
                r"(?<![A-Za-z0-9_])" + re.escape(tok) + r"(?![A-Za-z0-9_])",
                text,
                flags=re.I,
            )
        )
    return counts


def measure_child(cmd: list[str]) -> int:
    import resource
    import time

    start = time.perf_counter()
    proc = subprocess.run(cmd)
    wall = time.perf_counter() - start
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    print(
        "MEASURE " + json.dumps({"wall_seconds": round(wall, 3), "peak_rss_kb": rss}),
        file=sys.stderr,
    )
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


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    if argv[:2] == ["--measure", "--"]:
        return measure_child(argv[2:])
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--wrap", default="", help="optional launcher command placed before compiler invocations")
    ap.add_argument("--out", default=str(HERE / "lean_check_receipt.json"))
    args = ap.parse_args(argv)
    wrap = shlex.split(args.wrap)
    lean_bin = resolve_lean(args.lean)

    src = HERE / f"{MODULE}.lean"
    audit = HERE / f"{AUDIT}.lean"
    text = src.read_text(encoding="utf-8")
    tokens = scan_tokens(text)
    lines = text.splitlines()

    base_env = dict(os.environ)
    if "LEAN_SYSROOT" not in base_env:
        cand_sysroot = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1"
        if cand_sysroot.is_dir():
            base_env["LEAN_SYSROOT"] = str(cand_sysroot)

    ver = subprocess.run([lean_bin, "--version"], env=base_env, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    version_line = ver.stdout.decode("utf-8", "replace").strip()

    compile_flags = ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
    receipt: dict = {
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
        "imports": [l.split()[1] for l in lines if l.startswith("import ")],
        "forbidden_token_counts": tokens,
        "compile_flags": compile_flags,
    }
    ok = all(v == 0 for v in tokens.values())

    with tempfile.TemporaryDirectory(prefix="cold_blocks_nounwind_lean_") as tmp:
        olean = Path(tmp) / f"{MODULE}.olean"
        rc, out, err, wall, rss = timed(
            [lean_bin] + compile_flags + ["-o", str(olean), str(src)],
            base_env,
            wrap,
            HERE,
        )
        diagnostics = [
            l.replace(str(HERE), "<SUPPORT>")
            for l in (out + err).splitlines()
            if re.search(r": (error|warning)", l)
        ]
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
            env2 = dict(base_env, LEAN_PATH=tmp)
            rc2, out2, err2, wall2, rss2 = timed(
                [lean_bin, "-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", str(audit)],
                env2,
                wrap,
                HERE,
            )
            audit_json = None
            for line in (out2 + err2).splitlines():
                m = re.search(r"AUDIT (\{.*\})", line)
                if m:
                    audit_json = json.loads(m.group(1))
            axioms_printed = {}
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
