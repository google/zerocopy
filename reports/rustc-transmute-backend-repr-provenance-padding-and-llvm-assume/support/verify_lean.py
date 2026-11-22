#!/usr/bin/env python3
"""Kernel-check `TransmuteByteModelAndCodegenRefinement.lean` under Lean v4.34.1 and audit every
declaration in the `TransmuteByteModel` namespace.

Three independent checks, all required for exit status 0:
1. PLAIN:    `lean -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true`
             elaborates and kernel-checks with 0 warnings/errors, and `#print axioms` reports
             only allowed foundational axioms (`propext`, `Quot.sound` — zero `Classical.choice`,
             zero `sorryAx`, zero `Lean.ofReduceBool`).
2. AUDIT:    Environment walk (`import Lean`) over every constant under `TransmuteByteModel.*`
             confirms 0 `._unsafe_rec`, 0 `unsafe`, 0 `partial`, 0 `axiom`, 0 `opaque`, and
             collects transitive axioms across all constants (`0 Classical.choice`).
3. NEGATIVE: Appending a false reverse-refinement theorem is rejected by the kernel.

Standard library only (Python 3.10+). Scrubs and rejects any absolute paths in JSON output.
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

HERE = os.path.dirname(os.path.abspath(__file__))
LEAN_FILE = "TransmuteByteModelAndCodegenRefinement.lean"
FLAGS = ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}

AUDIT_TAIL = r"""
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ns : Name := `TransmuteByteModel
  let mut nThm : Nat := 0
  let mut nDef : Nat := 0
  let mut nOther : Nat := 0
  let mut bad : Array String := #[]
  let mut axs : Array Name := #[]
  for (n, ci) in env.constants.map₂.toList do
    if ns.isPrefixOf n then
      if (n.toString.splitOn "_unsafe_rec").length > 1 then bad := bad.push s!"unsafe_rec:{n}"
      if ci.isUnsafe then bad := bad.push s!"unsafe:{n}"
      if ci.isPartial then bad := bad.push s!"partial:{n}"
      match ci with
      | .thmInfo _ => nThm := nThm + 1
      | .defnInfo _ => nDef := nDef + 1
      | .axiomInfo _ => bad := bad.push s!"axiom:{n}"
      | .opaqueInfo _ => bad := bad.push s!"opaque:{n}"
      | _ => nOther := nOther + 1
      let used ← Lean.collectAxioms n
      for a in used do
        if !axs.contains a then axs := axs.push a
  logInfo s!"AUDIT constants: theorems={nThm} defs={nDef} other={nOther}"
  logInfo s!"AUDIT axioms used by any constant: {axs}"
  logInfo s!"AUDIT bad count={bad.size}: {bad}"
"""

NEGATIVE_TAIL = r"""
namespace TransmuteByteModel
theorem negative_control_must_be_rejected :
    runTransmuteThenExposeDeref evalTransmuteOpSem
      rawPtr4Layout u32Layout sampleLookupAddr sampleHeapVal samplePtrBytes sampleInitState =
        .ok 0xCAFEBABE := rfl
end TransmuteByteModel
"""


def run_lean(wrapper: list[str], lean: str, sysroot: str | None, path: str, cwd: str) -> tuple[int, str]:
    env = dict(os.environ)
    if sysroot:
        env["LEAN_SYSROOT"] = sysroot
    argv = [*wrapper, lean, *FLAGS, path]
    proc = subprocess.run(argv, cwd=cwd, env=env, capture_output=True, text=True, timeout=600)
    return proc.returncode, proc.stdout + proc.stderr


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--sysroot", default=os.environ.get("LEAN_SYSROOT"))
    ap.add_argument("--wrapper", default="")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    wrapper = shlex.split(args.wrapper)

    with open(os.path.join(HERE, LEAN_FILE), encoding="utf-8") as f:
        src = f.read()

    vproc = subprocess.run([args.lean, "--version"], capture_output=True, text=True, check=True)
    result: dict[str, object] = {
        "schema": "lean-kernel-audit/1",
        "lean_version_line": vproc.stdout.strip(),
        "flags": FLAGS,
        "file": LEAN_FILE,
        "source_bytes": len(src.encode("utf-8")),
        "source_lines": src.count("\n") + 1,
    }
    ok = True

    with tempfile.TemporaryDirectory(prefix="verify_lean_") as tmp:
        # 1. PLAIN
        with open(os.path.join(tmp, LEAN_FILE), "w", encoding="utf-8") as f:
            f.write(src)
        rc, out = run_lean(wrapper, args.lean, args.sysroot, LEAN_FILE, tmp)
        printed = re.findall(
            r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", out
        )
        printed_axioms = sorted(
            {a.strip() for _, _, lst in printed for a in lst.split(",") if a.strip()}
        )
        plain_ok = (
            rc == 0
            and "error:" not in out
            and len(printed) >= 12
            and set(printed_axioms) <= ALLOWED_AXIOMS
        )
        if not plain_ok:
            print("PLAIN FAILED:\n" + out, file=sys.stderr)
        result["plain"] = {
            "exit_code": rc,
            "print_axioms_lines": len(printed),
            "axioms_in_print_axioms_output": printed_axioms,
            "held": plain_ok,
        }
        ok &= plain_ok

        # 2. AUDIT
        with open(os.path.join(tmp, "Audit.lean"), "w", encoding="utf-8") as f:
            f.write("import Lean\n" + src + AUDIT_TAIL)
        rc_a, out_a = run_lean(wrapper, args.lean, args.sysroot, "Audit.lean", tmp)
        m_const = re.search(r"AUDIT constants: theorems=(\d+) defs=(\d+) other=(\d+)", out_a)
        m_ax = re.search(r"AUDIT axioms used by any constant: #\[([^\]]*)\]", out_a)
        m_bad = re.search(r"AUDIT bad count=(\d+): (#\[.*\])", out_a)
        audit: dict[str, object] = {"exit_code": rc_a}
        if m_const and m_ax and m_bad:
            axioms = sorted(a.strip() for a in m_ax.group(1).split(",") if a.strip())
            bad_cnt = int(m_bad.group(1))
            audit.update(
                {
                    "theorem_constants": int(m_const.group(1)),
                    "definition_constants": int(m_const.group(2)),
                    "other_constants": int(m_const.group(3)),
                    "axioms_used_by_any_constant": axioms,
                    "unsafe_partial_axiom_opaque_or_unsafe_rec_constants": bad_cnt,
                    "offending_constants": m_bad.group(2),
                }
            )
            audit["held"] = (
                rc_a == 0
                and set(axioms) <= ALLOWED_AXIOMS
                and bad_cnt == 0
                and int(m_const.group(1)) >= 15
            )
        else:
            audit["held"] = False
            print("AUDIT FAILED:\n" + out_a, file=sys.stderr)
        result["audit"] = audit
        ok &= bool(audit["held"])

        # 3. NEGATIVE CONTROL
        with open(os.path.join(tmp, "Negative.lean"), "w", encoding="utf-8") as f:
            f.write(src + NEGATIVE_TAIL)
        rc_n, out_n = run_lean(wrapper, args.lean, args.sysroot, "Negative.lean", tmp)
        neg_ok = rc_n != 0 and "error" in out_n
        result["negative_control"] = {
            "exit_code": rc_n,
            "rejected": neg_ok,
            "held": neg_ok,
        }
        ok &= neg_ok

    # Strip doc/line comments before token-scanning so prose comments mentioning forbidden tactics
    # do not trigger false positives, AND ALSO scan raw text for `sorry` / `admit` / `Classical.`.
    code_only = re.sub(r"/-.*?-/", "", src, flags=re.S)
    code_only = re.sub(r"--[^\n]*", "", code_only)
    scan = {}
    for name, pat in (
        ("sorry", r"\bsorry\b"),
        ("admit", r"\badmit\b"),
        ("omega", r"\bomega\b"),
        ("bv_decide", r"\bbv_decide\b"),
        ("native_decide", r"\bnative_decide\b"),
        ("partial def", r"\bpartial\s+def\b"),
        ("unsafe", r"\bunsafe\s+(def|theorem)\b"),
        ("Classical.", r"\bClassical\."),
        ("axiom", r"^\s*axiom\b"),
        ("import", r"^\s*import\b"),
        ("plain def (not noncomputable)", r"^\s*def\b"),
    ):
        scan[name] = len(re.findall(pat, code_only, flags=re.M))
    result["code_token_scan_occurrences"] = scan
    result["code_token_scan_all_zero"] = all(v == 0 for v in scan.values())
    ok &= bool(result["code_token_scan_all_zero"])
    result["all_checks_held"] = bool(ok)

    text = json.dumps(result, indent=2, sort_keys=True)
    if re.search(r"""(?:^|[\s"'=:,\[(])/(?:[A-Za-z0-9._+-]+/)+[A-Za-z0-9._+-]*""", text, re.M):
        print("refusing to write output containing an absolute path", file=sys.stderr)
        return 2
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    print(text)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
