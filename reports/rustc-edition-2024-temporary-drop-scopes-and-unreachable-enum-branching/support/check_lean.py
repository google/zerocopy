#!/usr/bin/env python3
"""Kernel-check `EditionDropScopesAndEnumBranching.lean` and write a receipt.

    python3 check_lean.py --out lean_verification_receipt.json -- <lean launcher...>

Everything after `--` is the command that starts Lean 4 (for example the path
to the `lean` binary of a v4.34.1 toolchain, optionally preceded by a resource
wrapper). The script appends

    -M2048 -DElab.async=false -Ddebug.skipKernelTC=false -DwarningAsError=true <file>

and runs Lean three times:

1. on the published file as-is;
2. on a temporary copy to which `#print axioms <name>` has been appended for
   every `theorem` in the file, so the receipt lists the axioms of all
   theorems, not only the ones the published file prints itself;
3. on a small census file that imports the compiled module together with the
   `Lean` library and walks every kernel constant the module declares
   (including compiler-generated auxiliaries), counting theorems, definitions,
   inductive types, axiom declarations, opaque constants, `unsafe` and
   `partial` constants, constants whose name contains `_unsafe_rec`,
   constants that mention `WellFounded.fix` (well-founded rather than
   structural recursion), and the union of axioms any constant depends on.

It also counts constructs that would weaken the result (`sorry`, `admit`,
`axiom`, `omega`, `decide`, `native_decide`, `bv_decide`, `partial`, `unsafe`,
`opaque`, `@[extern]`, `@[implemented_by]`, `Classical`) in the source with
comments removed. Exit status is non-zero if Lean fails, if any theorem or
other constant depends on an axiom other than `propext`, if any counted
construct occurs, or if the census finds an axiom declaration, an opaque,
`unsafe`, `partial` or `_unsafe_rec` constant, or a use of `WellFounded.fix`.

Standard library only; needs Python 3.10+.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import resource
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_FILE = "EditionDropScopesAndEnumBranching.lean"
NAMESPACE = "EditionDropScopesAndEnumBranching"
LEAN_FLAGS = ["-M2048", "-DElab.async=false", "-Ddebug.skipKernelTC=false", "-DwarningAsError=true"]
ALLOWED_AXIOMS = {"propext"}
FORBIDDEN = {
    "sorry": r"\bsorry\b",
    "admit": r"\badmit\b",
    "axiom_declaration": r"^\s*axiom\b",
    "omega": r"\bomega\b",
    "decide": r"\bdecide\b",
    "native_decide": r"\bnative_decide\b",
    "bv_decide": r"\bbv_decide\b",
    "partial": r"\bpartial\b",
    "unsafe": r"\bunsafe\b",
    "opaque": r"\bopaque\b",
    "extern_attribute": r"@\[\s*extern",
    "implemented_by_attribute": r"@\[\s*implemented_by",
    "Classical": r"\bClassical\b",
    "unsafe_rec": r"_unsafe_rec",
}


def strip_comments(src: str) -> str:
    """Remove nested `/- .. -/` block comments and `--` line comments."""
    out = []
    depth = 0
    i = 0
    while i < len(src):
        two = src[i : i + 2]
        if two == "/-":
            depth += 1
            i += 2
        elif two == "-/" and depth > 0:
            depth -= 1
            i += 2
        elif depth > 0:
            if src[i] == "\n":
                out.append("\n")
            i += 1
        elif two == "--":
            while i < len(src) and src[i] != "\n":
                i += 1
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


CENSUS_LEAN = """import Lean
import {module}
open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let some idx := env.getModuleIdx? `{module}
    | throwError "module not found"
  let data := env.header.moduleData[idx.toNat]!
  let mut axioms : Array Name := #[]
  let mut nAxiomDecl : Nat := 0
  let mut nOpaque : Nat := 0
  let mut nUnsafe : Nat := 0
  let mut nPartial : Nat := 0
  let mut nUnsafeRec : Nat := 0
  let mut nThm : Nat := 0
  let mut nDef : Nat := 0
  let mut nInduct : Nat := 0
  let mut nCtor : Nat := 0
  let mut nRec : Nat := 0
  let mut nWf : Nat := 0
  for ci in data.constants do
    if ci.getUsedConstantsAsSet.contains ``WellFounded.fix then nWf := nWf + 1
    if ci.isUnsafe then nUnsafe := nUnsafe + 1
    if ci.isPartial then nPartial := nPartial + 1
    if (ci.name.toString.splitOn "_unsafe_rec").length > 1 then nUnsafeRec := nUnsafeRec + 1
    match ci with
    | .axiomInfo _ => nAxiomDecl := nAxiomDecl + 1
    | .opaqueInfo _ => nOpaque := nOpaque + 1
    | .thmInfo _ => nThm := nThm + 1
    | .defnInfo _ => nDef := nDef + 1
    | .inductInfo _ => nInduct := nInduct + 1
    | .ctorInfo _ => nCtor := nCtor + 1
    | .recInfo _ => nRec := nRec + 1
    | .quotInfo _ => pure ()
    for a in (← Lean.collectAxioms ci.name) do
      unless axioms.contains a do axioms := axioms.push a
  logInfo m!"CENSUS constants={{data.constants.size}} theorems={{nThm}} definitions={{nDef}} inductives={{nInduct}} constructors={{nCtor}} recursors={{nRec}} axiom_declarations={{nAxiomDecl}} opaque={{nOpaque}} unsafe={{nUnsafe}} partial={{nPartial}} unsafe_rec={{nUnsafeRec}} well_founded_fix_users={{nWf}} axioms_used={{axioms.qsort Name.lt}}"
"""


def run_census(launcher: list[str], src: str) -> dict:
    """Compile the module to an .olean in a scratch directory and census it."""
    with tempfile.TemporaryDirectory(prefix="lean_census_") as tmp:
        tmp_dir = Path(tmp)
        (tmp_dir / LEAN_FILE).write_text(src)
        build = subprocess.run(
            [*launcher, *LEAN_FLAGS, "-o", f"{NAMESPACE}.olean", LEAN_FILE],
            cwd=tmp_dir, capture_output=True, text=True,
        )
        (tmp_dir / "Census.lean").write_text(CENSUS_LEAN.format(module=NAMESPACE))
        census = subprocess.run(
            [*launcher, "-M2048", "Census.lean"],
            cwd=tmp_dir, capture_output=True, text=True,
            env={**os.environ, "LEAN_PATH": str(tmp_dir)},
        )
    out = census.stdout + census.stderr
    result: dict = {"build_rc": build.returncode, "census_rc": census.returncode}
    m = re.search(r"CENSUS (.*)", out)
    if m:
        for key, value in re.findall(r"(\w+)=(\[[^\]]*\]|\d+)", m.group(1)):
            if value.startswith("["):
                result[key] = sorted(v.strip() for v in value[1:-1].split(",") if v.strip())
            else:
                result[key] = int(value)
    return result


def run_lean(launcher: list[str], cwd: Path, file_name: str) -> dict:
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.monotonic()
    proc = subprocess.run([*launcher, *LEAN_FLAGS, file_name], cwd=cwd, capture_output=True, text=True)
    wall = time.monotonic() - t0
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    return {
        "rc": proc.returncode,
        "wall_seconds": round(wall, 3),
        "child_user_cpu_seconds": round(after.ru_utime - before.ru_utime, 3),
        "children_max_rss_kib_high_water": after.ru_maxrss,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
    }


def parse_axioms(output: str) -> dict[str, list[str]]:
    result: dict[str, list[str]] = {}
    flat = re.sub(r"\n\s+", " ", output)
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", flat):
        result[m.group(1)] = sorted(a.strip() for a in m.group(2).split(",") if a.strip())
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", flat):
        result[m.group(1)] = []
    return result


def main() -> int:
    argv = sys.argv[1:]
    if "--" not in argv:
        print(__doc__, file=sys.stderr)
        return 2
    split = argv.index("--")
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    args = ap.parse_args(argv[:split])
    launcher = argv[split + 1 :]
    if not launcher:
        print("missing Lean launcher after `--`", file=sys.stderr)
        return 2

    src_path = HERE / LEAN_FILE
    src = src_path.read_text()
    code = strip_comments(src)
    theorems = re.findall(r"^theorem\s+(\S+)", code, re.M)
    declarations = {
        "theorem": len(theorems),
        "def": len(re.findall(r"^(?:noncomputable\s+)?def\s", code, re.M)),
        "noncomputable_def": len(re.findall(r"^noncomputable\s+def\s", code, re.M)),
        "abbrev": len(re.findall(r"^abbrev\s", code, re.M)),
        "inductive": len(re.findall(r"^inductive\s", code, re.M)),
        "structure": len(re.findall(r"^structure\s", code, re.M)),
    }
    forbidden_counts = {name: len(re.findall(rx, code, re.M)) for name, rx in FORBIDDEN.items()}
    imports = re.findall(r"^import\s+(\S+)", code, re.M)

    version = subprocess.run([launcher[-1], "--version"], capture_output=True, text=True).stdout.strip()

    as_published = run_lean(launcher, HERE, LEAN_FILE)

    with tempfile.TemporaryDirectory(prefix="lean_axioms_") as tmp:
        tmp_dir = Path(tmp)
        extra = "".join(f"open {NAMESPACE} in\n#print axioms {name}\n" for name in theorems)
        (tmp_dir / LEAN_FILE).write_text(src.rstrip("\n") + "\n" + extra)
        all_axioms_run = run_lean(launcher, tmp_dir, LEAN_FILE)

    census = run_census(launcher, src)

    axioms = {
        name.removeprefix(NAMESPACE + "."): deps
        for name, deps in parse_axioms(all_axioms_run["stdout"] + all_axioms_run["stderr"]).items()
    }
    missing = sorted(set(theorems) - set(axioms))
    union = sorted({a for deps in axioms.values() for a in deps})
    disallowed = sorted(set(union) - ALLOWED_AXIOMS)
    diagnostics = [
        l for l in (as_published["stdout"] + as_published["stderr"]).splitlines()
        if re.search(r": (error|warning)", l)
    ]

    def scrub(text: str) -> str:
        return text.replace(str(Path.home()), "<home>").replace(str(HERE), "<support>")

    receipt = {
        "schema": "lean-verification-receipt/1",
        "file": LEAN_FILE,
        "file_sha256": hashlib.sha256(src.encode("utf-8")).hexdigest(),
        "file_bytes": len(src.encode("utf-8")),
        "file_lines": src.count("\n"),
        "lean_version": version,
        "lean_binary": os.path.basename(launcher[-1]),
        "launched_through_wrapper": len(launcher) > 1,
        "lean_flags": LEAN_FLAGS,
        "imports": imports,
        "declarations": declarations,
        "forbidden_construct_counts_outside_comments": forbidden_counts,
        "as_published": {
            "rc": as_published["rc"],
            "wall_seconds": as_published["wall_seconds"],
            "child_user_cpu_seconds": as_published["child_user_cpu_seconds"],
            "children_max_rss_kib_high_water": as_published["children_max_rss_kib_high_water"],
            "error_or_warning_lines": [scrub(l) for l in diagnostics],
        },
        "all_theorems_axiom_run": {
            "rc": all_axioms_run["rc"],
            "wall_seconds": all_axioms_run["wall_seconds"],
            "theorems_reported": len(axioms),
            "theorems_missing_from_report": missing,
        },
        "axioms_by_theorem": dict(sorted(axioms.items())),
        "axiom_union": union,
        "theorems_without_any_axiom": sorted(n for n, deps in axioms.items() if not deps),
        "disallowed_axioms": disallowed,
        "kernel_constant_census": census,
    }
    ok = (
        as_published["rc"] == 0
        and all_axioms_run["rc"] == 0
        and not missing
        and not disallowed
        and not any(forbidden_counts.values())
        and not imports
        and census.get("build_rc") == 0
        and census.get("census_rc") == 0
        and all(
            census.get(k) == 0
            for k in ("axiom_declarations", "opaque", "unsafe", "partial", "unsafe_rec", "well_founded_fix_users")
        )
        and set(census.get("axioms_used", ["?"])) <= ALLOWED_AXIOMS
    )
    receipt["ok"] = ok
    Path(args.out).write_text(json.dumps(receipt, indent=2, sort_keys=True, ensure_ascii=True) + "\n")
    print(
        f"ok={ok} rc={as_published['rc']} theorems={len(theorems)} axiom_union={union} "
f"forbidden={ {k: v for k, v in forbidden_counts.items() if v} } wall={as_published['wall_seconds']}s "
        f"census={census}"
    )
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
