#!/usr/bin/env python3
"""Check `LintCapAndForbidUnsafeSoundness.lean` and audit its environment.

Steps, each recorded in the JSON transcript:

1. Scan the proof file's text for tokens that would make its claims weaker
   than they read (unfinished proofs, arithmetic or bit-vector decision
   procedures, compiled-code evaluation, classical choice, definitions
   accepted without a termination proof, added axioms, imports).
2. Run `lean` on the proof file with kernel type checking on, asynchronous
   elaboration off and warnings as errors, writing an `.olean` to a temporary
   directory, and collect the `#print axioms` lines.
3. Run `lean` on `EnvAudit.lean`, which loads that `.olean` and inspects every
   declared constant and the axioms reachable from it.

Usage:
    python3 verify_lean.py [--out lean_verification.json]

Environment:
    LEAN         lean binary (default: `lean` on PATH); expected Lean 4.34.1
    LEAN_PREFIX  optional command prefix (for example a resource limiter),
                 split on whitespace and placed before each lean invocation

Exit status is 0 only when all three steps succeed.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
PROOF = "LintCapAndForbidUnsafeSoundness.lean"
AUDIT = "EnvAudit.lean"
MODULE = "LintCapAndForbidUnsafeSoundness"
LEAN_FLAGS = ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]

# Regular expressions over the proof file's text; every count must be zero.
FORBIDDEN_TOKENS = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "omega": r"\bomega\b",
    "bv_decide": r"\bbv_decide\b",
    "native_decide": r"\bnative_decide\b",
    "decide +native": r"\bdecide\s*\+native\b",
    "Classical": r"\bClassical\b",
    "partial def": r"\bpartial\s+def\b",
    "unsafe def": r"\bunsafe\s+(def|theorem|instance)\b",
    "_unsafe_rec": r"_unsafe_rec",
    "axiom declaration": r"^\s*axiom\b",
    "implemented_by": r"\bimplemented_by\b",
    "extern": r"@\[\s*extern\b",
    "import": r"^\s*import\b",
    "opaque": r"^\s*opaque\b",
}
ALLOWED_AXIOMS = {"propext", "Quot.sound"}


def run(argv, cwd, env):
    proc = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, errors="replace")
    return proc.returncode, proc.stdout + proc.stderr


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--out", default="lean_verification.json")
    args = parser.parse_args()

    lean = os.environ.get("LEAN", "lean")
    prefix = shlex.split(os.environ.get("LEAN_PREFIX", ""))
    report: dict = {"schema": "lean-verification/1", "proof_file": PROOF, "audit_file": AUDIT,
                    "lean_flags": LEAN_FLAGS, "resource_prefix_used": bool(prefix)}
    ok = True

    rc, version = run([lean, "--version"], HERE, None)
    report["lean_version"] = version.strip()
    if rc != 0:
        print(f"cannot run {lean} --version", file=sys.stderr)
        return 2

    # 1. token scan
    text = (HERE / PROOF).read_text(encoding="utf-8")
    counts = {name: len(re.findall(pattern, text, re.M)) for name, pattern in FORBIDDEN_TOKENS.items()}
    report["token_scan"] = {"counts": counts, "ok": all(v == 0 for v in counts.values()),
                            "lines": text.count("\n"), "theorems": len(re.findall(r"^theorem\b", text, re.M))}
    ok &= report["token_scan"]["ok"]

    with tempfile.TemporaryDirectory(prefix="lean_verify_") as tmp:
        def scrub(s: str) -> str:
            for path, token in ((tmp, "$TMP"), (str(HERE), "$SUPPORT"), (os.path.expanduser("~"), "$HOME")):
                s = s.replace(path, token)
            return s

        # 2. elaborate + kernel check, emit .olean
        olean = str(Path(tmp) / f"{MODULE}.olean")
        argv = [lean] + LEAN_FLAGS + ["--root=" + str(HERE), "-o", olean, str(HERE / PROOF)]
        rc, out = run(prefix + argv, HERE, None)
        axiom_lines = [line for line in out.splitlines() if "depend" in line and line.startswith("'")]
        used = set()
        for line in axiom_lines:
            match = re.search(r"depends on axioms: \[(.*)\]", line)
            if match:
                used |= {a.strip() for a in match.group(1).split(",")}
        other_output = [line for line in out.splitlines() if line.strip() and line not in axiom_lines]
        report["proof_check"] = {
            "argv": ["lean"] + [scrub(a) for a in argv[1:]], "rc": rc,
            "print_axioms": axiom_lines,
            "axioms_used": sorted(used),
            "axiom_free": sum("does not depend on any axioms" in line for line in axiom_lines),
            "other_output": [scrub(line) for line in other_output],
            "ok": rc == 0 and used <= ALLOWED_AXIOMS and bool(axiom_lines),
        }
        ok &= report["proof_check"]["ok"]

        # 3. environment audit
        env = dict(os.environ, LEAN_PATH=tmp)
        argv = [lean] + LEAN_FLAGS + [str(HERE / AUDIT)]
        rc, out = run(prefix + argv, HERE, env) if report["proof_check"]["rc"] == 0 else (1, "skipped")
        summary = [line for line in out.splitlines() if "ENV_AUDIT_OK" in line]
        report["env_audit"] = {
            "argv": ["LEAN_PATH=$TMP", "lean"] + [scrub(a) for a in argv[1:]], "rc": rc,
            "output": [scrub(line) for line in out.splitlines() if line.strip()],
            "ok": rc == 0 and len(summary) == 1,
        }
        ok &= report["env_audit"]["ok"]

    report["ok"] = bool(ok)
    Path(args.out).write_text(json.dumps(report, indent=2, ensure_ascii=True) + "\n", encoding="utf-8")
    print(json.dumps({"ok": report["ok"], "token_scan": report["token_scan"]["ok"],
                      "proof_check": report["proof_check"]["ok"], "env_audit": report["env_audit"]["ok"],
                      "axioms_used": report["proof_check"]["axioms_used"]}))
    for line in report["env_audit"]["output"]:
        print(line)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
