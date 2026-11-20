#!/usr/bin/env python3
"""Recompute and verify Lean 4 axiom and statement/closure hash audits.

Copies `lean/` into a temporary directory, builds it with `lake build`, runs a
Lean 4 environment inspection program, and verifies that:
  1. Every non-internal declaration defined in the package's `[[lean_lib]]`
     modules uses only {propext, Classical.choice, Quot.sound}, declares no
     `axiom` or `opaque`, and matches `audit/axioms.json`.
  2. Every Lean declaration referenced by `results.json` exists and matches
     `audit/statements.json` on `statement_sha256`, `closure_sha256`, and
     `closure_size`.

Hashing algorithm (matching `audit/statements.json`):
  - Package predicate `inPkg env n`: the defining module of `n` has a library
    root declared in `lean/lakefile.toml` (`[[lean_lib]]`) as a prefix.
  - Statement hash (`statement_sha256`): SHA-256 of UTF-8 `toString (repr ci.type)`.
  - Definition closure: transitive DFS starting from `ci.type.getUsedConstants`
    restricted to constants `c` satisfying `inPkg env c`; for each such `c`
    with `ConstantInfo` `cc`, traverse `cc.type.getUsedConstants`, plus
    `v.getUsedConstants` when `cc.value? (allowOpaque := true) = some v` and
    `!cc.isTheorem`, plus `iv.ctors` when `cc` is `.inductInfo iv`.
  - Closure serialization: for each `c` in the closure, format
    `c.toString ++ " : " ++ toString (repr cc.type)` and, when `!cc.isTheorem`
    and `cc.value? (allowOpaque := true) = some v`, append
    `" := " ++ toString (repr v)`. Sort the resulting lines lexicographically,
    join with `"\n"`, UTF-8 encode, and take SHA-256 (`closure_sha256`);
    `closure_size` is the number of constants in the closure.

Usage:
  python3 audit/verify_audit.py [package_dir]
"""
import argparse
import hashlib
import json
import os
import re
import shlex
import shutil
import subprocess
import sys
import tempfile

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

AUDIT_LEAN_TEMPLATE = r"""
import Lean
{imports}
open Lean Elab Command

private def allowedRoots : List Name := [{roots}]
private def resultNames : List Name := [{results}]

private def inPkg (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some idx =>
    let m := env.header.moduleNames[idx.toNat]!
    allowedRoots.any (fun r => r.isPrefixOf m)
  | none => false

private def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

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
  for (n, ci) in env.constants.toList do
    if inPkg env n && !n.isInternal then
      let axs ← collectAxioms n
      decls := decls.push (Json.mkObj [("name", toJson n.toString), ("kind", toJson (kindOf ci)),
        ("axioms", toJson (axs.map Name.toString))])
  let mut stmts : Array Json := #[]
  for n in resultNames do
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
  IO.println ("AUDIT_JSON " ++ (Json.mkObj [("decls", Json.arr decls), ("stmts", Json.arr stmts)]).compress)
"""


def lib_roots(lean_dir):
    txt = open(os.path.join(lean_dir, "lakefile.toml"), encoding="utf-8").read()
    return [m.group(1) for m in re.finditer(r"\[\[lean_lib\]\][^\[]*?name\s*=\s*\"([^\"]+)\"", txt, re.S)]


def collect_card_names(results):
    names = set()
    for r in results:
        for key in ("lean", "lean_names", "nonvacuity_witness_lean", "positive_control_lean"):
            v = r.get(key)
            for n in ([v] if isinstance(v, str) else (v or [])):
                names.add(n)
        for h in r.get("hypotheses", []):
            ce = h.get("counterexample")
            for n in ([ce] if isinstance(ce, str) else (ce or [])):
                names.add(n)
    return sorted(names)


def lean_name_literal(n):
    parts = n.split(".")
    return "`" + ".".join(f"«{p}»" if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_'!?]*", p) else p for p in parts)


def main():
    default_pkg = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    ap = argparse.ArgumentParser(description="Verify Lean axioms and statement/closure SHA-256 hashes.")
    ap.add_argument("package_dir", nargs="?", default=default_pkg)
    ap.add_argument("--build-prefix", default="", help="Optional command prefix for `lake build`.")
    ap.add_argument("--lean-prefix", default="", help="Optional command prefix for `lake env lean`.")
    args = ap.parse_args()

    pkg = os.path.abspath(args.package_dir)
    lean_dir = os.path.join(pkg, "lean")
    results = json.load(open(os.path.join(pkg, "results.json"), encoding="utf-8"))
    expected_axioms = json.load(open(os.path.join(pkg, "audit", "axioms.json"), encoding="utf-8"))
    expected_stmts = json.load(open(os.path.join(pkg, "audit", "statements.json"), encoding="utf-8"))

    roots = lib_roots(lean_dir)
    card_names = collect_card_names(results)

    tmp = tempfile.mkdtemp(prefix="verify_audit_")
    try:
        work = os.path.join(tmp, "lean")
        shutil.copytree(lean_dir, work, ignore=shutil.ignore_patterns(".lake", "build"))

        build_cmd = shlex.split(args.build_prefix) + ["lake", "build"]
        b = subprocess.run(build_cmd, cwd=work, capture_output=True, text=True)
        if b.returncode != 0:
            sys.stderr.write(b.stdout + b.stderr)
            return 1

        imports = "\n".join(f"import {r}" for r in roots)
        src = AUDIT_LEAN_TEMPLATE.format(
            imports=imports,
            roots=", ".join(lean_name_literal(r) for r in roots),
            results=", ".join(lean_name_literal(n) for n in card_names),
        )
        with open(os.path.join(work, "VerifyAudit.lean"), "w", encoding="utf-8") as fh:
            fh.write(src)

        lean_cmd = shlex.split(args.lean_prefix) + ["lake", "env", "lean", "VerifyAudit.lean"]
        a = subprocess.run(lean_cmd, cwd=work, capture_output=True, text=True)
        m = re.search(r"AUDIT_JSON (\{.*\})", a.stdout)
        if a.returncode != 0 or not m:
            sys.stderr.write(a.stdout + a.stderr)
            return 1
        data = json.loads(m.group(1))
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    errors = []
    for d in data["decls"]:
        bad_ax = sorted(set(d["axioms"]) - ALLOWED_AXIOMS)
        if bad_ax:
            errors.append(f"disallowed axioms in {d['name']}: {bad_ax}")
        if d["kind"] in ("axiom", "opaque"):
            errors.append(f"forbidden {d['kind']} declaration: {d['name']}")

    recomputed_axioms = {d["name"]: sorted(d["axioms"]) for d in data["decls"]}
    if recomputed_axioms != expected_axioms["declarations"]:
        errors.append("recomputed axioms differ from audit/axioms.json")

    recomputed_stmts = {}
    for s in data["stmts"]:
        if s.get("missing"):
            errors.append(f"missing declaration referenced in results.json: {s['name']}")
            continue
        recomputed_stmts[s["name"]] = {
            "statement_sha256": hashlib.sha256(s["type_repr"].encode("utf-8")).hexdigest(),
            "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode("utf-8")).hexdigest(),
            "closure_size": len(s["closure"]),
        }

    exp_map = expected_stmts["statements"]
    for n in sorted(set(exp_map) | set(recomputed_stmts)):
        if exp_map.get(n) != recomputed_stmts.get(n):
            errors.append(f"statement/closure hash mismatch for {n}")

    if errors:
        for e in errors:
            print(f"FAIL: {e}", file=sys.stderr)
        return 1

    print(
        f"Verified {len(recomputed_axioms)} declarations against audit/axioms.json "
        f"and {len(recomputed_stmts)} statement/closure SHA-256 hashes against audit/statements.json: OK."
    )
    return 0


if __name__ == "__main__":
    sys.exit(main())
