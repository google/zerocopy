#!/usr/bin/env python3
"""Re-check `BoxDerefCallGuardsAndReturnDupSoundness.lean` and audit what the kernel accepted.

Three independent checks, each of which must hold for exit status 0:

1. PLAIN     The file elaborates and kernel-checks with warnings as errors.
2. AUDIT     A copy with `import Lean` prepended and an environment walk appended reports, for
             EVERY constant the file adds (not just hand-picked theorems): the union of axioms
             used, and any constant that is `unsafe`, `partial`, an `axiom`, an `opaque`, or a
             compiler helper named `*._unsafe_rec`.
3. NEGATIVE  A copy with a false theorem appended is REJECTED. This guards against a checker
             invocation that silently accepts everything.

A text scan for tactic names (`omega`, `bv_decide`, `native_decide`, `sorry`) is also reported.
It is a statement about the source text only; checks 1-3 are the statements about the proofs.

Usage:
    python3 verify_lean.py --lean /path/to/lean [--wrapper "cmd --flag --"] [--out result.json]

Standard library only (Python 3.10+). Temporary files are created in a TemporaryDirectory.
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
LEAN_FILE = "BoxDerefCallGuardsAndReturnDupSoundness.lean"
FLAGS = ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
ALLOWED_AXIOMS = {"propext", "Quot.sound"}
NAMESPACE = "BoxDerefCallGuards"

AUDIT_TAIL = r'''
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ns : Name := `BoxDerefCallGuards
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
      let as ← Lean.collectAxioms n
      for a in as do
        if !axs.contains a then axs := axs.push a
  logInfo s!"AUDIT constants: theorems={nThm} defs={nDef} other={nOther}"
  logInfo s!"AUDIT axioms used by any constant: {axs}"
  logInfo s!"AUDIT bad count={bad.size}: {bad}"
'''

# False: an arbitrary program has critical output edges (see `ce1Prog` in the file itself).
NEGATIVE_TAIL = r'''
namespace BoxDerefCallGuards
theorem negative_control_must_be_rejected (p : Prog) : NoCriticalOutEdge p.cfg := by
  intro x i y dst hOut x' s' hEdge
  exact ⟨rfl, rfl⟩
end BoxDerefCallGuards
'''


def run_lean(wrapper, lean, path, cwd):
    argv = [*wrapper, lean, *FLAGS, path]
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True, timeout=1800)
    return p.returncode, p.stdout + p.stderr


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawTextHelpFormatter)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--wrapper", default="", help="optional command prefix (e.g. a resource limiter)")
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    wrapper = shlex.split(args.wrapper)

    with open(os.path.join(HERE, LEAN_FILE), encoding="utf-8") as f:
        src = f.read()

    vrc, vout = subprocess.run([args.lean, "--version"], capture_output=True, text=True).returncode, \
        subprocess.run([args.lean, "--version"], capture_output=True, text=True).stdout.strip()
    result = {"lean_version_line": vout, "flags": FLAGS, "file": LEAN_FILE,
              "source_bytes": len(src.encode("utf-8")), "source_lines": src.count("\n") + 1}
    ok = True

    with tempfile.TemporaryDirectory(prefix="verify_lean_") as tmp:
        # 1. PLAIN
        plain = os.path.join(tmp, LEAN_FILE)
        with open(plain, "w", encoding="utf-8") as f:
            f.write(src)
        rc, out = run_lean(wrapper, args.lean, LEAN_FILE, tmp)
        printed = re.findall(r"'([^']+)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", out)
        printed_axioms = sorted({a.strip() for _, _, lst in printed for a in lst.split(",") if a.strip()})
        plain_ok = rc == 0 and "error" not in out and set(printed_axioms) <= ALLOWED_AXIOMS
        result["plain"] = {"exit_code": rc, "print_axioms_lines": len(printed),
                           "axioms_in_print_axioms_output": printed_axioms, "held": plain_ok}
        ok &= plain_ok

        # 2. AUDIT
        with open(os.path.join(tmp, "Audit.lean"), "w", encoding="utf-8") as f:
            f.write("import Lean\n" + src + AUDIT_TAIL)
        rc, out = run_lean(wrapper, args.lean, "Audit.lean", tmp)
        m_const = re.search(r"AUDIT constants: theorems=(\d+) defs=(\d+) other=(\d+)", out)
        m_ax = re.search(r"AUDIT axioms used by any constant: #\[([^\]]*)\]", out)
        m_bad = re.search(r"AUDIT bad count=(\d+): (#\[.*\])", out)
        audit = {"exit_code": rc}
        if m_const and m_ax and m_bad:
            axioms = sorted(a.strip() for a in m_ax.group(1).split(",") if a.strip())
            audit.update({
                "theorem_constants": int(m_const.group(1)), "definition_constants": int(m_const.group(2)),
                "other_constants": int(m_const.group(3)), "axioms_used_by_any_constant": axioms,
                "unsafe_partial_axiom_opaque_or_unsafe_rec_constants": int(m_bad.group(1)),
                "offending_constants": m_bad.group(2),
            })
            audit["held"] = (rc == 0 and set(axioms) <= ALLOWED_AXIOMS and int(m_bad.group(1)) == 0
                             and int(m_const.group(1)) > 0)
        else:
            audit["held"] = False
            audit["note"] = "audit output not found"
        result["audit"] = audit
        ok &= audit["held"]

        # 3. NEGATIVE
        with open(os.path.join(tmp, "Negative.lean"), "w", encoding="utf-8") as f:
            f.write(src + NEGATIVE_TAIL)
        rc, out = run_lean(wrapper, args.lean, "Negative.lean", tmp)
        neg_ok = rc != 0 and "error" in out and "negative_control" not in re.sub(r"error.*", "", out)
        result["negative_control"] = {"exit_code": rc, "rejected": rc != 0 and "error" in out,
                                      "held": rc != 0 and "error" in out}
        ok &= result["negative_control"]["held"]

    # text scan (about the source text only)
    scan = {}
    for name, pat in (("sorry", r"\bsorry\b"), ("admit", r"\badmit\b"), ("omega", r"\bomega\b"),
                      ("bv_decide", r"\bbv_decide\b"), ("native_decide", r"\bnative_decide\b"),
                      ("partial def", r"\bpartial\s+def\b"), ("unsafe", r"\bunsafe\s+(def|theorem)\b"),
                      ("Classical.", r"\bClassical\."), ("axiom", r"^\s*axiom\b"),
                      ("import", r"^import\b"), ("plain def (not noncomputable)", r"^def\b")):
        scan[name] = len(re.findall(pat, src, flags=re.M))
    result["source_text_scan_occurrences"] = scan
    result["source_text_scan_all_zero"] = all(v == 0 for v in scan.values())
    ok &= result["source_text_scan_all_zero"]
    result["all_checks_held"] = bool(ok)

    text = json.dumps(result, indent=1, sort_keys=True)
    # Any absolute POSIX path (a slash that starts a token, then at least one directory segment).
    if re.search(r"""(?:^|[\s"'=:,\[(])/(?:[A-Za-z0-9._+-]+/)+[A-Za-z0-9._+-]*""", text, re.M):
        print("refusing to write output containing an absolute path", file=sys.stderr)
        return 2
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text + "\n")
    print(text)
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
