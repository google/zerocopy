#!/usr/bin/env python3
"""Count proof holes and global assumptions in Coq sources (comments stripped).

Usage: python3 count_proof_holes.py <checkout-root> <file.v>...
Counts, per file and in total, occurrences outside (* ... *) comments of:
  Admitted.  admit.  Axiom/Axioms  Parameter/Parameters  Conjecture  Hypothesis/Hypotheses
A Parameter inside a Module Type is a functor argument, not a global axiom; the
report distinguishes these by inspection.
"""
import os
import re
import sys

PATS = {
    "Admitted.": r"\bAdmitted\.",
    "admit.": r"\badmit\.",
    "Axiom": r"^\s*Axioms?\b",
    "Parameter": r"^\s*Parameters?\b",
    "Conjecture": r"^\s*Conjecture\b",
    "Hypothesis": r"^\s*Hypothes[ie]s\b",
}


def strip_comments(s):
    out, depth, i = [], 0, 0
    while i < len(s):
        if s.startswith("(*", i):
            depth += 1
            i += 2
            continue
        if depth and s.startswith("*)", i):
            depth -= 1
            i += 2
            continue
        if depth == 0 or s[i] == "\n":
            out.append(s[i])
        i += 1
    return "".join(out)


def main():
    root, files = sys.argv[1], sys.argv[2:]
    total = {k: 0 for k in PATS}
    lines = 0
    for f in files:
        s = open(os.path.join(root, f), encoding="utf-8", errors="replace").read()
        lines += s.count("\n")
        c = strip_comments(s)
        r = {k: len(re.findall(p, c, re.M)) for k, p in PATS.items()}
        for k in PATS:
            total[k] += r[k]
        if any(r.values()):
            print(f, r)
    print("TOTAL", total, "files:", len(files), "newline-count:", lines)


if __name__ == "__main__":
    main()
