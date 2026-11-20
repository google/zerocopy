#!/usr/bin/env python3
"""Compile `atomic_lowering_probe.rs` under several target/feature configurations
and record, per probe function, the LLVM IR instructions and the assembly
instructions that rustc emits.

Standard library only. Usage:

    python3 run_live_probe.py --rustc "$(rustup which rustc)" --out live_probe_results.json

A configuration whose target has no installed `core` is recorded with its
compiler error instead of being silently skipped.
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
PROBE = os.path.join(HERE, "atomic_lowering_probe.rs")

# (configuration name, target triple, extra flags)
CONFIGS = [
    ("x86_64_O3", "x86_64-unknown-linux-gnu", ["-C", "opt-level=3"]),
    ("x86_64_O3_no_redzone", "x86_64-unknown-linux-gnu",
     ["-C", "opt-level=3", "-C", "no-redzone=yes"]),
    ("x86_64_O0", "x86_64-unknown-linux-gnu", ["-C", "opt-level=0"]),
    ("aarch64_v80_default_outline_O3", "aarch64-unknown-linux-gnu", ["-C", "opt-level=3"]),
    ("aarch64_v80_no_outline_O3", "aarch64-unknown-linux-gnu",
     ["-C", "opt-level=3", "-C", "target-feature=-outline-atomics"]),
    ("aarch64_lse_O3", "aarch64-unknown-linux-gnu",
     ["-C", "opt-level=3", "-C", "target-feature=+lse"]),
    ("aarch64_lse_rcpc_O3", "aarch64-unknown-linux-gnu",
     ["-C", "opt-level=3", "-C", "target-feature=+lse,+rcpc"]),
    ("aarch64_lse_rcpc3_O3", "aarch64-unknown-linux-gnu",
     ["-C", "opt-level=3", "-C", "target-feature=+lse,+rcpc,+rcpc3"]),
    ("i686_default_sse2_O3", "i686-unknown-linux-gnu", ["-C", "opt-level=3"]),
    ("i686_nosse2_O3", "i686-unknown-linux-gnu",
     ["-C", "opt-level=3", "-C", "target-feature=-sse2,-sse"]),
    ("i686_sse1_only_O3", "i686-unknown-linux-gnu",
     ["-C", "opt-level=3", "-C", "target-feature=-sse2"]),
    ("s390x_O3", "s390x-unknown-linux-gnu", ["-C", "opt-level=3"]),
]

FN_RE = re.compile(r"^#\[no_mangle\]\s*(?:\n\s*)?pub fn ([A-Za-z0-9_]+)", re.M)


def probe_functions() -> list[str]:
    with open(PROBE, encoding="utf-8") as f:
        return FN_RE.findall(f.read())


def comment_marker(target: str) -> str:
    # `#` starts a comment in x86 AT&T syntax and s390x output, but is the
    # immediate prefix in AArch64 output, where `//` starts a comment.
    return "//" if target.startswith("aarch64") else "#"


def asm_bodies(text: str, target: str, wanted: set[str]) -> dict[str, list[str]]:
    marker = comment_marker(target)
    out: dict[str, list[str]] = {}
    cur = None
    for raw in text.splitlines():
        line = raw.split(marker, 1)[0].rstrip()
        stripped = line.strip()
        if not stripped:
            continue
        m = re.match(r"^([A-Za-z_][A-Za-z0-9_.$]*):$", stripped)
        if m and not stripped.startswith("."):
            cur = m.group(1) if m.group(1) in wanted else None
            if cur is not None:
                out[cur] = []
            continue
        if cur is None:
            continue
        if stripped.startswith(".cfi_endproc") or stripped.startswith(".Lfunc_end"):
            cur = None
            continue
        if stripped.startswith(".") or stripped.endswith(":"):
            continue  # directives and local labels
        out[cur].append(stripped)
    return out


def ir_bodies(text: str, wanted: set[str] | None) -> dict[str, list[str]]:
    out: dict[str, list[str]] = {}
    cur = None
    for raw in text.splitlines():
        m = re.match(r"^define .*@\"?([A-Za-z0-9_.$]+)\"?\(", raw)
        if m:
            name = m.group(1)
            cur = name if (wanted is None or name in wanted) else None
            if cur is not None:
                out[cur] = []
            continue
        if raw.startswith("}"):
            cur = None
            continue
        if cur is None:
            continue
        s = raw.strip()
        if not s or s.endswith(":") or s.startswith(";"):
            continue
        out[cur].append(s)
    return out


ATOMIC_IR = re.compile(r"\b(load atomic|store atomic|atomicrmw|cmpxchg|fence)\b")


def run_config(rustc: str, name: str, target: str, flags: list[str], fns: list[str]) -> dict:
    wanted = set(fns)
    with tempfile.TemporaryDirectory() as tmp:
        cmd = [rustc, "--edition=2021", "--crate-type=rlib", "--crate-name=atomics",
               "--target", target, *flags, "--emit=asm,llvm-ir", "--out-dir", tmp, PROBE]
        proc = subprocess.run(cmd, capture_output=True, text=True)
        rec: dict = {
            "target": target,
            "extra_flags": flags,
            "returncode": proc.returncode,
            # Diagnostic headlines only (lines that start a warning or an error).
            "diagnostics": [l for l in proc.stderr.splitlines()
                            if l.startswith(("warning", "error"))],
        }
        if proc.returncode != 0:
            return rec
        with open(os.path.join(tmp, "atomics.s"), encoding="utf-8") as f:
            asm_text = f.read()
        with open(os.path.join(tmp, "atomics.ll"), encoding="utf-8") as f:
            ir_text = f.read()
    asm = asm_bodies(asm_text, target, wanted)
    ir = ir_bodies(ir_text, wanted)
    rec["functions"] = {fn: {"llvm_ir": ir.get(fn), "asm": asm.get(fn)} for fn in fns}
    if "opt-level=0" in flags:
        # Without inlining the probe wrappers only call into `core`; record the
        # atomic IR instructions of every other function in the module.
        callee = {}
        for fn, body in ir_bodies(ir_text, None).items():
            if fn in wanted:
                continue
            hits = [l for l in body if ATOMIC_IR.search(l) and not l.startswith("call")]
            if hits:
                callee[fn] = hits
        rec["unoptimized_callee_atomic_ir"] = callee
    return rec


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--rustc", default="rustc")
    ap.add_argument("--out", default=os.path.join(HERE, "live_probe_results.json"))
    args = ap.parse_args()

    version = subprocess.run([args.rustc, "-vV"], capture_output=True, text=True).stdout
    vinfo = {}
    for line in version.splitlines():
        if ": " in line:
            k, v = line.split(": ", 1)
            vinfo[k] = v
    fns = probe_functions()
    result = {
        "probe": "atomic_lowering_probe.rs",
        "observed_utc": datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
        "rustc_version_line": version.splitlines()[0] if version else "",
        "rustc_commit_hash": vinfo.get("commit-hash"),
        "rustc_release": vinfo.get("release"),
        "llvm_version": vinfo.get("LLVM version"),
        "host": vinfo.get("host"),
        "function_count": len(fns),
        "configs": {},
    }
    for name, target, flags in CONFIGS:
        result["configs"][name] = run_config(args.rustc, name, target, flags, fns)
        rc = result["configs"][name]["returncode"]
        print(f"{name}: rc={rc}", file=sys.stderr)
    with open(args.out, "w", encoding="utf-8") as f:
        json.dump(result, f, indent=1, sort_keys=True)
        f.write("\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
