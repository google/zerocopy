#!/usr/bin/env python3
"""ISLa (pinned revision) generation probe.

(1) Classic length-prefixed record: <rec> ::= <len> ":" <data>, constraint
    str.to.int(<len>) = str.len(<data>). Generates N inputs, times generation, and
    re-checks every input with the solver's own `check`.
(2) cell_methods-like strings: grammar "<name>: <method><tail>" where <tail> may be
    empty or junk. Each generated string is tested with the cell_methods pattern
    copied verbatim from compliance-checker (pinned revision, cf_1_6.py) using
    `regex.match` (as the checker does) and `regex.fullmatch` (reference).
"""
import time, sys
import regex
from isla.solver import ISLaSolver

N = int(sys.argv[1]) if len(sys.argv) > 1 else 50

LEN_GRAMMAR = {
    "<start>": ["<rec>"],
    "<rec>": ["<len>:<data>"],
    "<len>": ["<digit>", "<digit><digit>"],
    "<digit>": [str(i) for i in range(10)],
    "<data>": ["<chr>", "<chr><data>"],
    "<chr>": ["a", "b", "c"],
}
LEN_CONSTRAINT = 'str.to.int(<len>) = str.len(<data>)'

def run_len():
    s = ISLaSolver(LEN_GRAMMAR, LEN_CONSTRAINT, max_number_free_instantiations=1, max_number_smt_instantiations=1)
    out = []; t0 = time.perf_counter()
    for _ in range(N):
        try:
            out.append(str(s.solve()))
        except StopIteration:
            break
    gen = time.perf_counter() - t0
    t1 = time.perf_counter()
    ok = sum(1 for x in out if s.check(x))
    chk = time.perf_counter() - t1
    bad = s.check("3:ab")
    print(f"[len-prefix] generated={len(out)} distinct={len(set(out))} gen_wall={gen:.2f}s "
          f"({len(out)/gen:.1f} inputs/s) recheck_ok={ok}/{len(out)} check_wall={chk:.2f}s check('3:ab')={bad}")
    print("   sample:", out[:6])

CM_GRAMMAR = {
    "<start>": ["<cm>"],
    "<cm>": ["<name>: <method><tail>"],
    "<name>": ["time", "area", "lat"],
    "<method>": ["mean", "sum", "point", "maximum"],
    "<tail>": ["", " ;;; DROP", " junk", ";"],
}
# Verbatim from compliance_checker/cf/cf_1_6.py (pinned revision), check_cell_methods.
PSEP = regex.compile(
    r"(?P<vars>\w+: )+(?P<method>\w+) ?(?P<where>where (?P<wtypevar>\w+) "
    r"?(?P<over>over (?P<otypevar>\w+))?| ?)(?:\((?P<paren_contents>[^)]*)\))?",
)

def run_cm():
    s = ISLaSolver(CM_GRAMMAR, 'true', max_number_free_instantiations=10)
    seen = set(); t0 = time.perf_counter()
    for _ in range(60):
        try:
            seen.add(str(s.solve()))
        except StopIteration:
            break
    gen = time.perf_counter() - t0
    prefix_only = sorted(x for x in seen if regex.match(PSEP, x) and not regex.fullmatch(PSEP, x))
    print(f"[cell_methods] distinct={len(seen)} gen_wall={gen:.2f}s accepted_by_prefix_match_but_not_fullmatch={len(prefix_only)}")
    print("   examples:", prefix_only[:5])

run_len()
run_cm()
