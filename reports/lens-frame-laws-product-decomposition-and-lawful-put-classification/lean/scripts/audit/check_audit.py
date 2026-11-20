#!/usr/bin/env python3
"""Compare the output of scripts/audit/Audit.lean with the recorded audit files.

Usage (from the package's lean/ directory, after `lake build`):

    lake env lean scripts/audit/Audit.lean > /tmp/lens_audit.out
    python3 scripts/audit/check_audit.py /tmp/lens_audit.out ../audit

For every name referenced by results.json, the statement hash is the SHA-256 of
the `repr` of its type, and the closure hash is the SHA-256 of the sorted,
newline-joined list of the statements and definition bodies of the library
constants that its type reaches.  Exit status 0 iff every recorded hash and
every recorded axiom list matches.
"""
import hashlib
import json
import re
import sys


def main():
    out_path, audit_dir = sys.argv[1], sys.argv[2]
    m = re.search(r"LENS_AUDIT_JSON (\{.*\})", open(out_path, encoding="utf-8").read())
    if not m:
        print("no audit output found")
        return 1
    audit = json.loads(m.group(1))
    computed = {
        s["name"]: {
            "statement_sha256": hashlib.sha256(s["type_repr"].encode()).hexdigest(),
            "closure_sha256": hashlib.sha256("\n".join(s["closure"]).encode()).hexdigest(),
            "closure_size": len(s["closure"]),
        }
        for s in audit["stmts"]
    }
    recorded = json.load(open(f"{audit_dir}/statements.json", encoding="utf-8"))["statements"]
    drift = sorted(n for n in set(recorded) | set(computed) if recorded.get(n) != computed.get(n))
    axioms = {d["name"]: sorted(d["axioms"]) for d in audit["decls"]}
    recorded_axioms = json.load(open(f"{audit_dir}/axioms.json", encoding="utf-8"))["declarations"]
    ax_drift = sorted(n for n in set(axioms) | set(recorded_axioms)
                      if axioms.get(n) != recorded_axioms.get(n))
    print(json.dumps({"statements_checked": len(computed), "statement_drift": drift,
                      "declarations_checked": len(axioms), "axiom_drift": ax_drift}, indent=2))
    return 0 if not drift and not ax_drift else 1


if __name__ == "__main__":
    sys.exit(main())
