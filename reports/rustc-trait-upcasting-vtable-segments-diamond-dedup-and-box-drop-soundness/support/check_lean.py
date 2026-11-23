#!/usr/bin/env python3
"""Verify `TraitUpcastingVtableSegmentsAndBoxDropSoundness.lean` synchronously with
Lean v4.34.1 (`-DwarningAsError=true`), enforce pure `noncomputable def` discipline
and zero forbidden tokens/tactics, run MetaM audit over `env.constants.map₁` and
`modData.constNames`, clean transient `.olean`s, and emit `lean_check_receipt.json`.

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
    ("_unsafe_rec", r"_unsafe_rec"),
    ("axiom_decl", r"^\s*axiom\b"),
    ("opaque_decl", r"^\s*opaque\b"),
    ("unsafe_kw", r"\bunsafe\b"),
    ("extern_attr", r"@\[extern"),
    ("deriving_decidable_or_repr", r"\bderiving\b[^\n]*(?:DecidableEq|Repr)"),
]

MIN_LOC = 900


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments(src: str) -> str:
    """Strip Lean line (`-- ...`) and nested block (`/- ... -/`) comments."""
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


def check_all_defs_noncomputable(code_only: str) -> list[str]:
    """Ensure every top-level/namespace `def` uses `noncomputable def`."""
    bad: list[str] = []
    for idx, line in enumerate(code_only.splitlines(), start=1):
        # Match lines starting with optional modifiers followed by `def <ident>`
        m = re.match(r"^\s*(?:(?:private|protected)\s+)?def\s+([A-Za-z0-9_.']+)", line)
        if m:
            bad.append(f"L{idx}: {m.group(1)}")
    return bad


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


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--lean",
        default=str(Path.home() / ".elan/toolchains/leanprover--lean4---v4.34.1/bin/lean"),
        help="Path to lean executable",
    )
    parser.add_argument(
        "--wrapper",
        default=str(Path.home() / ".local/bin/anneal-lean-run"),
        help="Optional wrapper command prefix (set '' to disable)",
    )
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Output JSON receipt path (default: support/lean_check_receipt.json)",
    )
    args = parser.parse_args()

    support_dir = Path(__file__).resolve().parent
    module_path = support_dir / "TraitUpcastingVtableSegmentsAndBoxDropSoundness.lean"
    audit_path = support_dir / "TraitUpcastingVtableSegmentsAudit.lean"
    out_path = args.out.resolve() if args.out else (support_dir / "lean_check_receipt.json")

    src = module_path.read_text(encoding="utf-8")
    code_only = strip_comments(src)

    token_hits: dict[str, int] = {}
    for label, pat in FORBIDDEN_PATTERNS:
        matches = re.findall(pat, code_only, flags=re.M)
        token_hits[label] = len(matches)

    plain_defs = check_all_defs_noncomputable(code_only)
    token_hits["plain_def_without_noncomputable"] = len(plain_defs)

    prefix: list[str] = (
        [args.wrapper, "--mode", "file", "--"] if args.wrapper and Path(args.wrapper).exists() else []
    )
    base_env = os.environ.copy()
    lean_path_root = str(Path(args.lean).resolve().parent.parent)
    base_env.setdefault("LEAN_SYSROOT", lean_path_root)

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
    with tempfile.TemporaryDirectory(prefix="lean_upcast_check_") as tmp_str:
        tmp = Path(tmp_str)
        olean_path = tmp / "TraitUpcastingVtableSegmentsAndBoxDropSoundness.olean"

        compile_cmd = [
            *prefix,
            args.lean,
            *flags,
            f"--root={support_dir}",
            "-o",
            str(olean_path),
            str(module_path),
        ]
        compile_proc, compile_sec, compile_rss_kb = run_timed(compile_cmd, env=base_env, cwd=support_dir)

        audit_env = base_env.copy()
        existing_lp = audit_env.get("LEAN_PATH", "")
        audit_env["LEAN_PATH"] = f"{tmp}:{existing_lp}" if existing_lp else str(tmp)
        audit_cmd = [*prefix, args.lean, *flags, f"--root={support_dir}", str(audit_path)]
        audit_proc, audit_sec, audit_rss_kb = run_timed(audit_cmd, env=audit_env, cwd=support_dir)

        olean_bytes = olean_path.stat().st_size if olean_path.exists() else 0

    audit_kv: dict[str, str] = {}
    for line in audit_proc.stdout.splitlines():
        if "=" in line and line.startswith("AUDIT_"):
            k, v = line.split("=", 1)
            audit_kv[k.strip()] = v.strip()

    src_lines = src.splitlines()
    src_bytes = module_path.stat().st_size
    theorem_decls = len(re.findall(r"^\s*theorem\s+", code_only, flags=re.M))
    nc_def_decls = len(re.findall(r"^\s*(?:(?:private|protected)\s+)?noncomputable\s+def\s+", code_only, flags=re.M))
    type_decls = len(re.findall(r"^\s*(?:inductive|structure)\s+", code_only, flags=re.M))

    ok = (
        len(src_lines) >= MIN_LOC
        and all(v == 0 for v in token_hits.values())
        and compile_proc.returncode == 0
        and compile_proc.stdout.strip() == ""
        and compile_proc.stderr.strip() == ""
        and audit_proc.returncode == 0
        and audit_kv.get("AUDIT_VIOLATIONS") == "0"
        and audit_kv.get("AUDIT_MAP1_MODULE_UNSAFE_REC") == "0"
    )

    receipt: dict[str, Any] = {
        "lean_version": lean_version,
        "flags": flags,
        "module": "TraitUpcastingVtableSegmentsAndBoxDropSoundness.lean",
        "module_sha256": sha256_file(module_path),
        "audit_sha256": sha256_file(audit_path),
        "source_metrics": {
            "lines": len(src_lines),
            "min_loc_required": MIN_LOC,
            "bytes": src_bytes,
            "theorem_decls": theorem_decls,
            "noncomputable_def_decls": nc_def_decls,
            "inductive_and_structure_decls": type_decls,
        },
        "forbidden_token_hits": token_hits,
        "plain_defs_found": plain_defs,
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
