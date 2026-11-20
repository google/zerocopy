#!/usr/bin/env python3
"""Summarize jps_batch output (JSON lines) into the tables used in the report."""
import json, statistics as st, sys
rows = [json.loads(l) for l in open(sys.argv[1])]
def fmt(xs, nd=2):
    xs = [x for x in xs if x is not None]
    if not xs: return "n/a"
    if len(xs) == 1: return f"{xs[0]:.{nd}f}"
    return f"{st.mean(xs):.{nd}f} [{min(xs):.{nd}f}-{max(xs):.{nd}f}]"
print("## dt sweep (3 seeds each): model | dt | completed | t50 s | t90 s | evac s | dmin m | max overlap m | backward-step frac | errors | wall s/run | us per agent-iteration")
for m in ["SFM", "GCFM", "CFSM", "AVM"]:
    for dt in [0.005, 0.01, 0.02, 0.05, 0.1]:
        rs = [r for r in rows if r.get("study") == "dt" and r["model"] == m and r["dt"] == dt]
        errs = sorted(set((r.get("error") or "")[:60] for r in rs if r.get("error")))
        comp = sum(1 for r in rs if r.get("evac_time") is not None)
        stuck = [r.get("remaining") for r in rs if r.get("evac_time") is None and not r.get("error")]
        us = [1e6 * r["wall_s"] / r["agent_iterations"] for r in rs if r.get("agent_iterations")]
        print(f"{m} | {dt} | {comp}/{len(rs)} (stuck remaining={stuck}) | {fmt([r.get('t50') for r in rs])} | {fmt([r.get('t90') for r in rs])} | {fmt([r.get('evac_time') for r in rs])} | {fmt([r.get('min_center_distance') for r in rs],3)} | {fmt([r.get('max_overlap') for r in rs],3)} | {fmt([r.get('backward_step_fraction') for r in rs],3)} | {errs} | {fmt([r['wall_s'] for r in rs],1)} | {fmt(us,1)}")
print()
print("## +/-10% perturbation at dt=0.01 (3 seeds): model | param | factor | t50 | t90 | evac | completed | dmin | maxov")
for m in ["SFM", "GCFM", "CFSM", "AVM"]:
    base = [r for r in rows if r.get("study") == "dt" and r["model"] == m and r["dt"] == 0.01]
    print(f"{m} | baseline | 1.0 | {fmt([r.get('t50') for r in base])} | {fmt([r.get('t90') for r in base])} | {fmt([r.get('evac_time') for r in base])} | {sum(1 for r in base if r.get('evac_time') is not None)}/{len(base)} | {fmt([r.get('min_center_distance') for r in base],3)} | {fmt([r.get('max_overlap') for r in base],3)}")
    params = sorted(set(r["param"] for r in rows if r.get("study") == "perturb" and r["model"] == m))
    for p in params:
        for f in (0.9, 1.1):
            rs = [r for r in rows if r.get("study") == "perturb" and r["model"] == m and r["param"] == p and r["factor"] == f]
            errs = sorted(set((r.get("error") or "")[:50] for r in rs if r.get("error")))
            print(f"{m} | {p} | {f} | {fmt([r.get('t50') for r in rs])} | {fmt([r.get('t90') for r in rs])} | {fmt([r.get('evac_time') for r in rs])} | {sum(1 for r in rs if r.get('evac_time') is not None)}/{len(rs)} | {fmt([r.get('min_center_distance') for r in rs],3)} | {fmt([r.get('max_overlap') for r in rs],3)} {errs}")
