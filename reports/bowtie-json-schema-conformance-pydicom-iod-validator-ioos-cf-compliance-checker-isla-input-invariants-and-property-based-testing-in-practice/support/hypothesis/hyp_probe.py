#!/usr/bin/env python3
"""Toy fail-open validators vs. reference predicates, searched with Hypothesis.

These validators are illustrative toys written for this probe, not code from any
examined upstream project. Each pair encodes one fail-open mechanism; Hypothesis
`find` searches for an input on which the toy accepts but the reference rejects.
Run: venv_hyp/bin/python hyp_probe.py
"""
import math, time
from hypothesis import find, settings, strategies as st, HealthCheck

S = settings(max_examples=5000, derandomize=True, database=None,
             suppress_health_check=list(HealthCheck))

# M1 NaN comparison: "reject if out of range" written as two < tests.
def toy_in_range(x, lo=0.0, hi=100.0):
    return not (x < lo or x > hi)
def ref_in_range(x, lo=0.0, hi=100.0):
    return lo <= x <= hi            # every comparison with NaN is False

# M2 empty-collection quantification: spec says one or more values, all positive.
def toy_all_pos(xs):
    return all(v > 0 for v in xs)
def ref_all_pos(xs):
    return len(xs) > 0 and all(v > 0 for v in xs)

# M3 short-circuit on absence: optional-looking guard skips a required check.
UNITS = {"K", "degC", "m s-1"}
def toy_units(rec):
    return rec.get("units") is None or rec["units"] in UNITS
def ref_units(rec):
    return rec.get("units") in UNITS   # units is required

# M4 mis-associated logical operator: intended "neither a nor b".
def toy_neither(a, b):
    return not a or b
def ref_neither(a, b):
    return not (a or b)

# M5 prefix match: anchored at start only.
import re
PAT = re.compile(r"[a-z]+: (mean|sum|point)")
def toy_cell_methods(s):
    return PAT.match(s) is not None
def ref_cell_methods(s):
    return PAT.fullmatch(s) is not None

cases = [
    ("M1 NaN comparison", st.floats(allow_nan=True, allow_infinity=True),
     lambda x: toy_in_range(x) and not ref_in_range(x)),
    ("M2 empty collection", st.lists(st.integers(-5, 5), max_size=4),
     lambda xs: toy_all_pos(xs) and not ref_all_pos(xs)),
    ("M3 short-circuit absence", st.fixed_dictionaries({}, optional={"units": st.sampled_from(sorted(UNITS) + ["furlong"])}),
     lambda r: toy_units(r) and not ref_units(r)),
    ("M4 operator association", st.tuples(st.booleans(), st.booleans()),
     lambda ab: toy_neither(*ab) and not ref_neither(*ab)),
    ("M5 prefix match (random text)", st.text(alphabet="abt: mensu;X", max_size=20),
     lambda s: toy_cell_methods(s) and not ref_cell_methods(s)),
    # Same property, but inputs built from the attribute's grammar plus an arbitrary tail.
    ("M5 prefix match (grammar)", st.builds(lambda n, m, tail: f"{n}: {m}{tail}",
                                            st.from_regex(r"[a-z]{1,3}", fullmatch=True),
                                            st.sampled_from(["mean", "sum", "point"]),
                                            st.text(alphabet=" ;X", max_size=5)),
     lambda s: toy_cell_methods(s) and not ref_cell_methods(s)),
]
for name, strat, pred in cases:
    t0 = time.perf_counter()
    try:
        ex = find(strat, pred, settings=S)
        res = repr(ex)
    except Exception as e:  # NoSuchExample
        res = f"no counterexample ({type(e).__name__})"
    print(f"{name:28s} minimal counterexample: {res:28s} wall={time.perf_counter()-t0:.3f}s")
