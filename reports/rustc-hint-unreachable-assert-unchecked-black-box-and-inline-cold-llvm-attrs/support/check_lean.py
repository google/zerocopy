#!/usr/bin/env python3
"""Kernel-checked Lean v4.34.1 verification & MetaM purity audit runner."""

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import re
import resource
import subprocess
import sys
import tempfile
import time

HERE = pathlib.Path(__file__).resolve().parent
MAIN_LEAN = HERE / "HintAssumeBlackBoxAndInlineAttrsSoundness.lean"
AUDIT_LEAN = HERE / "HintAssumeBlackBoxAndInlineAttrsAudit.lean"
OUT_PATH = HERE / "lean_check_receipt.json"

FORBIDDEN_REGEXES = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "axiom": r"\baxiom\b",
    "opaque": r"\bopaque\b",
    "unsafe": r"\bunsafe\b",
    "partial": r"\bpartial\b",
    "implemented_by": r"\bimplemented_by\b",
    "extern": r"\bextern\b",
    "omega": r"\bomega\b",
    "bv_decide": r"\bbv_decide\b",
    "native_decide": r"\bnative_decide\b",
    "Classical.choice": r"\bClassical\.choice\b",
    "_unsafe_rec": r"\._unsafe_rec\b",
    "noncomputable section": r"\bnoncomputable\s+section\b",
    "deriving": r"\bderiving\b",
}


def sanitize(text: str, tmp_dir: pathlib.Path) -> str:
    home = str(pathlib.Path.home())
    return text.replace(str(tmp_dir), "<tmp>").replace(home, "<home>")


def find_lean_and_wrapper() -> tuple[str, str | None, str]:
    toolchain = pathlib.Path.home() / ".elan" / "toolchains" / "leanprover--lean4---v4.34.1"
    lean_bin = str(toolchain / "bin" / "lean")
    wrapper_path = pathlib.Path.home() / ".local" / "bin" / "anneal-lean-run"
    wrapper = str(wrapper_path) if wrapper_path.exists() else None
    return lean_bin, wrapper, str(toolchain)


def timed_run(cmd: list[str], env: dict[str, str], wrapper: str | None, cwd: pathlib.Path) -> tuple[int, str, str, float, int]:
    full_cmd = [wrapper, "--mode", "file", "--", *cmd] if wrapper else cmd
    t0 = time.monotonic()
    r = subprocess.run(full_cmd, cwd=cwd, env=env, capture_output=True, text=True)
    dt = round(time.monotonic() - t0, 3)
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    return r.returncode, r.stdout, r.stderr, dt, rss


def main() -> int:
    lean_bin, wrapper, sysroot = find_lean_and_wrapper()
    src = MAIN_LEAN.read_text(encoding="utf-8")
    src_sha256 = hashlib.sha256(src.encode("utf-8")).hexdigest()
    loc = len(src.splitlines())

    forbidden_counts = {
        tok: len(re.findall(pat, src))
        for tok, pat in FORBIDDEN_REGEXES.items()
    }
    plain_defs = [
        f"L{idx}: {line.strip()}"
        for idx, line in enumerate(src.splitlines(), 1)
        if re.match(r"^\s*(?:private\s+|protected\s+)?def\b", line)
    ]

    lean_ver = subprocess.run([lean_bin, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    base_env = dict(os.environ, LEAN_SYSROOT=sysroot)

    with tempfile.TemporaryDirectory() as td_str:
        td = pathlib.Path(td_str)
        olean = td / "HintAssumeBlackBoxAndInlineAttrsSoundness.olean"
        rc1, out1, err1, dt1, rss1 = timed_run(
            [
                lean_bin,
                "-M2048",
                "-DElab.async=false",
                "-Ddebug.skipKernelTC=false",
                "-DwarningAsError=true",
                "-o",
                str(olean),
                str(MAIN_LEAN),
            ],
            base_env,
            wrapper,
            HERE,
        )
        diag_lines = [l for l in (out1 + "\n" + err1).splitlines() if ": error" in l or ": warning" in l]
        errors = sum(1 for l in diag_lines if ": error" in l)
        warnings = sum(1 for l in diag_lines if ": warning" in l)

        receipt = {
            "lean_version": lean_ver,
            "wrapper_used": wrapper is not None,
            "file": MAIN_LEAN.name,
            "loc": loc,
            "source_sha256": src_sha256,
            "forbidden_token_counts": forbidden_counts,
            "plain_non_noncomputable_defs": plain_defs,
            "compile": {
                "exit_code": rc1,
                "errors": errors,
                "warnings": warnings,
                "wall_seconds": dt1,
                "peak_rss_kb": rss1,
                "olean_bytes": olean.stat().st_size if olean.exists() else None,
                "first_diagnostics": [sanitize(l, td) for l in diag_lines[:25]],
            },
        }

        ok = (
            rc1 == 0
            and errors == 0
            and warnings == 0
            and loc >= 1100
            and all(v == 0 for v in forbidden_counts.values())
            and len(plain_defs) == 0
        )

        if rc1 == 0:
            env2 = dict(base_env, LEAN_PATH=str(td))
            rc2, out2, err2, dt2, rss2 = timed_run(
                [lean_bin, "-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", str(AUDIT_LEAN)],
                env2,
                wrapper,
                HERE,
            )
            audit_json = None
            for line in (out2 + "\n" + err2).splitlines():
                m = re.search(r"AUDIT\s+(\{.*\})", line)
                if m:
                    audit_json = json.loads(m.group(1))
            axioms_printed = {}
            for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out2 + "\n" + err2):
                axioms_printed[m.group(1)] = [a.strip() for a in m.group(2).split(",")]
            for m in re.finditer(r"'([^']+)' does not depend on any axioms", out2 + "\n" + err2):
                axioms_printed[m.group(1)] = []
            violations = [
                line.strip()
                for line in (out2 + "\n" + err2).splitlines()
                if re.match(
                    r"\s*(theorem .* depends on forbidden axiom:|axiom constant:|opaque constant:|quot constant:|non-safe definition:|unsafe_rec helper:)",
                    line,
                )
            ]
            receipt["audit"] = {
                "exit_code": rc2,
                "summary": audit_json,
                "violation_lines": violations,
                "print_axioms": axioms_printed,
                "wall_seconds": dt2,
                "peak_rss_kb": rss2,
            }
            ok = ok and rc2 == 0 and audit_json is not None and audit_json["violations"] == 0

    receipt["passed"] = bool(ok)
    OUT_PATH.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
