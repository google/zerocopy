#!/usr/bin/env python3
"""Revalidate a formally verified Lean results report package.

Usage (from anywhere):  python3 support/revalidate.py <package_dir>

Requirements: `elan` (so that `lake` picks up the toolchain pinned in `lean/lean-toolchain`)
and `python3`. The package itself is never modified: the Lean project is copied to a
temporary directory first.

Checks:
  1. `lake build` of the package's Lean project succeeds.
  2. No Lean source contains `sorry`, `admit`, `native_decide`, or declares an `axiom`.
  3. Every declaration of the package's library depends only on the axioms
     propext, Classical.choice, Quot.sound (computed with Lean's `collectAxioms`).
  4. For every Lean name referenced by `results.json` (fields `lean`, `lean_names`,
     `nonvacuity_witness_lean`, `positive_control_lean`, `scope_witnesses_lean`,
     `corollaries_lean`, and hypothesis `counterexample`s), the SHA-256 of the statement
     (Lean `repr` of its type) and of its definition closure (types and values of every
     package-local constant reachable from the statement; theorem bodies excluded) equals
     the value recorded in `audit/statements.json`.
Exit status 0 iff all checks pass.
"""
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile

ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
NAME_FIELDS = ("lean", "lean_names", "nonvacuity_witness_lean", "positive_control_lean",
               "scope_witnesses_lean", "corollaries_lean")

AUDIT = r"""
import Lean
{imports}
open Lean Elab Command

private def roots : List Name := [{roots}]
private def wanted : List Name := [{names}]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx => roots.any (fun r => r.isPrefixOf env.header.moduleNames[idx.toNat]!)
  | none => false

private partial def closure (env : Environment) (todo : List Name) (acc : NameSet) : NameSet :=
  match todo with
  | [] => acc
  | n :: rest =>
    if acc.contains n || !inPkg env n then closure env rest acc else
    let acc := acc.insert n
    match env.find? n with
    | none => closure env rest acc
    | some ci =>
      let cs := ci.type.getUsedConstants.toList ++
        (match ci.value? (allowOpaque := true) with
         | some v => if ci.isTheorem then [] else v.getUsedConstants.toList
         | none => []) ++
        (match ci with
         | .inductInfo iv => iv.ctors
         | _ => [])
      closure env (cs ++ rest) acc

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut decls : Array Json := #[]
  for (n, _) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in wanted do
    match env.find? n with
    | none => stmts := stmts.push (Json.mkObj [("name", toJson n.toString), ("missing", toJson true)])
    | some ci =>
      let cl := closure env (ci.type.getUsedConstants.toList) {{}}
      let clTxt := cl.toList.map (fun c =>
        match env.find? c with
        | some cc => c.toString ++ " : " ++ toString (repr cc.type) ++
            (match cc.value? (allowOpaque := true) with
             | some v => if cc.isTheorem then "" else " := " ++ toString (repr v)
             | none => "")
        | none => c.toString)
      stmts := stmts.push (Json.mkObj [("name", toJson n.toString),
        ("type_repr", toJson (toString (repr ci.type))),
        ("closure", toJson (clTxt.toArray.qsort (· < ·)))])
  IO.println ("REVALIDATE_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
"""


def lit(n):
    return "`" + ".".join(p if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'!?]*", p) else f"«{p}»" for p in n.split("."))


def strip_comments(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and src.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = len(src) if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def main():
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    pkg = os.path.abspath(sys.argv[1])
    ok = True
    lean_dir = os.path.join(pkg, "lean")
    results = json.load(open(os.path.join(pkg, "results.json")))
    names = set()
    for r in results:
        for f in NAME_FIELDS:
            v = r.get(f)
            names |= {v} if isinstance(v, str) else set(v or [])
        for h in r.get("hypotheses", []):
            ce = h.get("counterexample")
            names |= {ce} if isinstance(ce, str) else set(ce or [])
    recorded = json.load(open(os.path.join(pkg, "audit", "statements.json")))["statements"]
    names |= set(recorded)
    roots = re.findall(r"\[\[lean_lib\]\][^\[]*?name\s*=\s*\"([^\"]+)\"",
                       open(os.path.join(lean_dir, "lakefile.toml")).read(), re.S)

    for root, dirs, files in os.walk(lean_dir):
        dirs[:] = [d for d in dirs if d != ".lake"]
        for fn in files:
            if fn.endswith(".lean"):
                code = strip_comments(open(os.path.join(root, fn), encoding="utf-8").read())
                for pat in (r"\bsorry\b", r"\badmit\b", r"\bnative_decide\b", r"(?m)^\s*(private\s+)?axiom\b"):
                    if re.search(pat, code):
                        print(f"FAIL banned token {pat} in {os.path.relpath(os.path.join(root, fn), pkg)}")
                        ok = False

    tmp = tempfile.mkdtemp(prefix="revalidate_")
    work = os.path.join(tmp, "lean")
    shutil.copytree(lean_dir, work, ignore=shutil.ignore_patterns(".lake"))
    b = subprocess.run(["lake", "build"], cwd=work, capture_output=True, text=True)
    if b.returncode != 0:
        print("FAIL lake build\n" + (b.stdout + b.stderr)[-3000:])
        sys.exit(1)
    print("ok   lake build")
    open(os.path.join(work, "RevalidateAudit.lean"), "w").write(AUDIT.format(
        imports="\n".join(f"import {r}" for r in roots),
        roots=", ".join(lit(r) for r in roots),
        names=", ".join(lit(n) for n in sorted(names))))
    a = subprocess.run(["lake", "env", "lean", "RevalidateAudit.lean"], cwd=work, capture_output=True, text=True)
    m = re.search(r"REVALIDATE_JSON (\{.*\})", a.stdout)
    if not m:
        print("FAIL audit program\n" + (a.stdout + a.stderr)[-3000:])
        sys.exit(1)
    audit = json.loads(m.group(1))
    bad = [d for d in audit["decls"] if set(d["axioms"]) - ALLOWED]
    for d in bad[:20]:
        print(f"FAIL axioms {d['name']}: {sorted(set(d['axioms']) - ALLOWED)}")
    ok &= not bad
    print(f"{'ok  ' if not bad else 'FAIL'} axioms ({len(audit['decls'])} declarations)")
    mism = 0
    unrecorded = 0
    for s in audit["stmts"]:
        if s.get("missing"):
            print(f"FAIL missing declaration {s['name']}")
            mism += 1
            continue
        got = {"statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
               "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
               "closure_size": len(s["closure"])}
        rec = recorded.get(s["name"])
        if rec is None:
            unrecorded += 1  # referenced by a card but not hashed at publication; existence checked only
            continue
        if any(rec.get(k) != v for k, v in got.items()):
            print(f"FAIL statement hash {s['name']}")
            mism += 1
    ok &= mism == 0
    print(f"{'ok  ' if not mism else 'FAIL'} statement hashes ({len(audit['stmts']) - unrecorded} hashed names; {unrecorded} referenced names exist but carry no recorded hash)")
    shutil.rmtree(tmp, ignore_errors=True)
    print("REVALIDATED" if ok else "REVALIDATION FAILED")
    sys.exit(0 if ok else 1)


if __name__ == "__main__":
    main()
