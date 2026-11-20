#!/usr/bin/env python3
"""Batch driver for jps_probe.py: time-step sweep and +/-10 % parameter perturbations.
Usage: PYTHONPATH=<dir containing pyjupedsim*.so> jps_batch.py <out.jsonl> [max_workers]"""
import concurrent.futures as cf
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = sys.argv[1]
WORKERS = int(sys.argv[2]) if len(sys.argv) > 2 else 32
SEEDS = [0, 1, 2]

cfgs = []
for m in ["SFM", "GCFM", "CFSM", "AVM"]:
    for dt in [0.005, 0.01, 0.02, 0.05, 0.1]:
        for s in SEEDS:
            cfgs.append({"study": "dt", "model": m, "dt": dt, "seed": s})
PERTURB = {
    "SFM": {"reaction_time": 0.5, "agent_scale": 2000.0, "v0": 1.2},
    "GCFM": {"strength_neighbor_repulsion": 0.3, "tau": 0.5, "v0": 1.2},
    "CFSM": {"time_gap": 1.0, "range_neighbor_repulsion": 0.1, "v0": 1.2},
    "AVM": {"time_gap": 1.06, "anticipation_time": 1.0, "v0": 1.2},
}
for m, ps in PERTURB.items():
    for p, base in ps.items():
        for f in (0.9, 1.1):
            for s in SEEDS:
                cfgs.append({"study": "perturb", "model": m, "dt": 0.01, "seed": s,
                             "param": p, "factor": f, "params": {p: round(base * f, 6)}})


def one(cfg):
    p = subprocess.run([sys.executable, os.path.join(HERE, "jps_probe.py"), json.dumps(cfg)],
                       capture_output=True, text=True, timeout=7200)
    if p.returncode != 0:
        return json.dumps(dict(cfg, error=f"rc={p.returncode} {p.stderr[-400:]}"))
    return p.stdout.strip()


with open(OUT, "w") as f, cf.ThreadPoolExecutor(WORKERS) as ex:
    for line in ex.map(one, cfgs):
        f.write(line + "\n")
        f.flush()
print("done", len(cfgs))
