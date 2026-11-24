#!/usr/bin/env python3
"""Verify `ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness.lean` synchronously with Lean v4.34.1,
enforce strict purity and `noncomputable def` policy on source tokens, run
`ImpliedBoundsRfc2093Audit.lean` over the compiled `.olean` in a temporary directory,
clean up `.olean` files, and emit a JSON receipt.

Uses Python 3.10+ standard library only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any

FORBIDDEN_PATTERNS: list[tuple[str, str]] = [
    ("sorry", r"\bsorry\b"),
    ("admit", r"\badmit\b"),
    ("Classical", r"\bClassical\b"),
    ("omega", r"\bomega\b"),
    ("bv_decide", r"\bbv_decide\b"),
    ("native_decide", r"\bnative_decide\b"),
    ("partial_def", r"\bpartial\s+def\b"),
    ("noncomputable_section", r"\bnoncomputable\s+section\b"),
    ("bare_def_without_noncomputable", r"^(?!\s*noncomputable\s+def\b)\s*(?:(?:private|protected)\s+)?def\b"),
    ("deriving", r"\bderiving\b"),
    ("_unsafe_rec", r"_unsafe_rec"),
    ("axiom_decl", r"^\s*axiom\b"),
    ("opaque_decl", r"^\s*opaque\b"),
    ("unsafe_kw", r"\bunsafe\b"),
    ("extern_attr", r"@\[extern"),
]


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(src: str) -> str:
    """Strip Lean line (`-- ...`) and block (`/- ... -/`) comments for code-only token checks."""
    out: list[str] = []
    i = 0
    n = len(src)
    depth = 0
    while i < n:
        if depth == 0 and src[i : i + 2] == "--":
            while i < n and src[i] != "\n":
                i += 1
        elif src[i : i + 2] == "/-":
            depth += 1
            i += 2
        elif depth > 0 and src[i : i + 2] == "-/":
            depth -= 1
            i += 2
        elif depth == 0:
            out.append(src[i])
            i += 1
        else:
            if src[i] == "\n":
                out.append("\n")
            i += 1
    return "".join(out)


def run_timed(
    cmd: list[str], env: dict[str, str] | None = None, cwd: Path | None = None
) -> tuple[subprocess.CompletedProcess[str], float, int | None]:
    t0 = time.monotonic()
    with tempfile.TemporaryFile(mode="w+t", encoding="utf-8") as out_f, tempfile.TemporaryFile(
        mode="w+t", encoding="utf-8"
    ) as err_f:
        proc = subprocess.Popen(
            cmd,
            env=env,
            cwd=str(cwd) if cwd else None,
            stdout=out_f,
            stderr=err_f,
        )
        _, status, rusage = os.wait4(proc.pid, 0)
        wall = time.monotonic() - t0
        out_f.seek(0)
        err_f.seek(0)
        stdout = out_f.read()
        stderr = err_f.read()
    rc = os.waitstatus_to_exitcode(status)
    rss_kb = int(rusage.ru_maxrss) if rusage and rusage.ru_maxrss else None
    return subprocess.CompletedProcess(cmd, rc, stdout, stderr), wall, rss_kb


def find_default_lean() -> str:
    candidate = Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"
    if candidate.is_file():
        return str(candidate)
    return "lean"


def find_default_wrapper() -> str | None:
    candidate = Path.home() / ".local/bin/anneal-lean-run"
    if candidate.is_file():
        return str(candidate)
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lean",
        default=find_default_lean(),
        help="Path to lean executable",
    )
    parser.add_argument(
        "--wrapper",
        default=find_default_wrapper(),
        help="Optional anneal-lean-run wrapper path",
    )
    parser.add_argument(
        "--no-wrapper",
        action="store_true",
        help="Invoke lean directly without anneal-lean-run wrapper",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output JSON receipt path (default: support/lean_check_receipt.json)",
    )
    args = parser.parse_args()

    support_dir = Path(__file__).resolve().parent
    module_path = support_dir / "ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness.lean"
    audit_path = support_dir / "ImpliedBoundsRfc2093Audit.lean"
    out_path = args.out.resolve() if args.out else (support_dir / "lean_check_receipt.json")

    src = module_path.read_text(encoding="utf-8")
    code_only = strip_comments(src)

    token_hits: dict[str, int] = {}
    for label, pat in FORBIDDEN_PATTERNS:
        matches = re.findall(pat, code_only, flags=re.M)
        token_hits[label] = len(matches)

    prefix: list[str] = []
    if args.wrapper and not args.no_wrapper:
        if Path(args.wrapper).name == "anneal-lean-run":
            prefix = [args.wrapper, "--mode", "file", "--"]
        else:
            prefix = [args.wrapper, "--"]

    base_env = os.environ.copy()
    lean_bin = Path(args.lean)
    if "LEAN_SYSROOT" not in base_env and lean_bin.parent.name == "bin":
        sysroot = lean_bin.parent.parent
        if sysroot.exists():
            base_env["LEAN_SYSROOT"] = str(sysroot)

    ver_proc = subprocess.run(
        [*prefix, args.lean, "--version"],
        env=base_env,
        capture_output=True,
        text=True,
        check=False,
    )
    if ver_proc.returncode != 0:
        print(f"ERROR: failed to query lean version: {ver_proc.stderr}", file=sys.stderr)
        return 1
    lean_version = ver_proc.stdout.strip()

    flags = ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
    with tempfile.TemporaryDirectory(prefix="lean_implied_bounds_check_") as tmp_str:
        tmp = Path(tmp_str)
        olean_path = tmp / "ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness.olean"

        compile_cmd = [
            *prefix,
            args.lean,
            *flags,
            f"--root={support_dir}",
            "-o",
            str(olean_path),
            str(module_path),
        ]
        compile_proc, compile_sec, compile_rss_kb = run_timed(
            compile_cmd, env=base_env, cwd=support_dir
        )

        audit_env = base_env.copy()
        existing_lp = audit_env.get("LEAN_PATH", "")
        audit_env["LEAN_PATH"] = f"{tmp}:{existing_lp}" if existing_lp else str(tmp)
        audit_cmd = [
            *prefix,
            args.lean,
            *flags,
            f"--root={support_dir}",
            str(audit_path),
        ]
        audit_proc, audit_sec, audit_rss_kb = run_timed(
            audit_cmd, env=audit_env, cwd=support_dir
        )

        olean_bytes = olean_path.stat().st_size if olean_path.exists() else 0

    audit_kv: dict[str, str] = {}
    for line in audit_proc.stdout.splitlines():
        if "=" in line and line.startswith("AUDIT_"):
            k, v = line.split("=", 1)
            audit_kv[k.strip()] = v.strip()

    src_lines = src.splitlines()
    src_bytes = module_path.stat().st_size
    theorem_decls = len(re.findall(r"^\s*theorem\s+", code_only, flags=re.M))
    noncomputable_def_decls = len(re.findall(r"^\s*noncomputable\s+def\s+", code_only, flags=re.M))
    bare_def_decls = token_hits.get("bare_def_without_noncomputable", 0)
    type_decls = len(re.findall(r"^\s*(?:inductive|structure)\s+", code_only, flags=re.M))

    ok = (
        all(v == 0 for v in token_hits.values())
        and noncomputable_def_decls > 0
        and bare_def_decls == 0
        and len(src_lines) >= 1100
        and compile_proc.returncode == 0
        and compile_proc.stdout.strip() == ""
        and compile_proc.stderr.strip() == ""
        and audit_proc.returncode == 0
        and audit_kv.get("AUDIT_VIOLATIONS") == "0"
        and audit_kv.get("AUDIT_UNSAFE_REC") == "0"
    )

    receipt: dict[str, Any] = {
        "lean_version": lean_version,
        "flags": flags,
        "module": "ImpliedBoundsRfc2093ProjectionAndSupertraitSoundness.lean",
        "module_sha256": sha256_file(module_path),
        "audit_sha256": sha256_file(audit_path),
        "source_metrics": {
            "lines": len(src_lines),
            "bytes": src_bytes,
            "theorem_decls": theorem_decls,
            "noncomputable_def_decls": noncomputable_def_decls,
            "bare_def_decls": bare_def_decls,
            "inductive_and_structure_decls": type_decls,
        },
        "forbidden_token_hits": token_hits,
        "compile": {
            "returncode": compile_proc.returncode,
            "wall_seconds": round(compile_sec, 3),
            "max_rss_kb": compile_rss_kb,
            "olean_bytes": olean_bytes,
            "stdout": compile_proc.stdout.strip(),
            "stderr": compile_proc.stderr.strip(),
        },
        "audit": {
            "returncode": audit_proc.returncode,
            "wall_seconds": round(audit_sec, 3),
            "max_rss_kb": audit_rss_kb,
            "summary": audit_kv,
            "stderr": audit_proc.stderr.strip(),
        },
        "passed": ok,
    }

    out_path.write_text(json.dumps(receipt, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(receipt, indent=2, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
