#!/usr/bin/env python3
"""Differential check of t-way coverage measurement: this package's own
counter (pict_probe.py) vs NIST CCMCL (usnistgov/combinatorial-testing-tools,
'CCM Command Line Tool/ccmcl.jar').  CCMCL needs a display (its Main class
builds a Swing JFrame in a static initializer), so it is run under xvfb-run.

Usage: python3 ccm_crosscheck.py <pict_probe_out_dir> <ccmcl_classpath> <workdir>
"""
import os
import re
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import pict_probe as pp  # noqa: E402

NAMES = [n for n, _ in pp.PARAMS]
IDX = {n: {v: i for i, v in enumerate(vals)} for n, vals in pp.PARAMS}

ACTS_CONSTRAINTS = [
    "Fault=4 => (Rule=4 || Rule=1)",
    "Fault=3 => (Rule=2 || Rule=0)",
    "Construct=4 => (Fault!=4 && Rule!=4)",
    "Construct=6 => Context!=0",
    "Fault=1 => (Construct=0 || Construct=1 || Construct=2 || Construct=3)",
]


def read_tsv(path):
    lines = [l for l in open(path).read().splitlines() if l.strip()]
    hdr = lines[0].split("\t")
    return [dict(zip(hdr, l.split("\t"))) for l in lines[1:]]


def acts_file(rows, constrained, path):
    out = ["[Parameter]"]
    for n, vals in pp.PARAMS:
        out.append("%s (int): %s" % (n, ",".join(str(i) for i in range(len(vals)))))
    out.append("")
    if constrained:
        out.append("[Constraint]")
        out.extend(ACTS_CONSTRAINTS)
        out.append("")
    out.append("[Test Set]")
    for r in rows:
        out.append(",".join(str(IDX[n][r[n]]) for n in NAMES))
    open(path, "w").write("\n".join(out) + "\n")


def run_ccm(cp, acts, ts, limit_s=180):
    """CCMCL prints its coverage table and then keeps the JVM alive (Swing
    frame), so stream stdout, stop once every requested 'Total t-way coverage'
    line has appeared (plus the following summary lines), then kill the whole
    process group."""
    import signal
    import time as _t
    cmd = ["xvfb-run", "-a", "java", "-cp", cp, "com.nist.ccmcl.Main", "-A", acts, "-T", ",".join(map(str, ts))]
    p = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True, start_new_session=True)
    os.set_blocking(p.stdout.fileno(), False)
    buf, t0, done_at = "", _t.time(), None
    while _t.time() - t0 < limit_s:
        try:
            chunk = p.stdout.read()
        except (BlockingIOError, TypeError):
            chunk = None
        if chunk:
            buf += chunk
        if done_at is None and all(("Total %d-way coverage" % t) in buf for t in ts):
            done_at = _t.time()
        if done_at is not None and _t.time() - done_at > 3:
            break
        if p.poll() is not None:
            break
        _t.sleep(0.2)
    try:
        os.killpg(p.pid, signal.SIGTERM)
        _t.sleep(1)
        os.killpg(p.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    res = {}
    for t in ts:
        m = re.search(r"Total %d-way coverage: ([0-9.]+)" % t, buf)
        res[t] = float(m.group(1)) if m else None
    return res, buf


def main():
    pdir, cp, work = sys.argv[1], sys.argv[2], sys.argv[3]
    os.makedirs(work, exist_ok=True)
    cases = []
    for cons in (False, True):
        tag = "c" if cons else "u"
        for t in (2, 3):
            rows = read_tsv(os.path.join(pdir, "array_t%d_%s.tsv" % (t, tag)))
            cases.append(("t%d_%s_full" % (t, tag), rows, cons, t))
            cases.append(("t%d_%s_evenrows" % (t, tag), rows[0::2], cons, t))
    print("case                 rows  t  own_covered/required  own_fraction  CCMCL_total")
    for name, rows, cons, t in cases:
        acts = os.path.join(work, name + ".txt")
        acts_file(rows, cons, acts)
        req = pp.required_tuples(t, cons)
        cov = pp.tuples_of(rows, t, NAMES) & req
        res, out = run_ccm(cp, acts, [t])
        open(os.path.join(work, name + ".ccmcl.out"), "w").write(out)
        print("%-20s %4d  %d  %4d/%4d            %.5f       %s" % (
            name, len(rows), t, len(cov), len(req), len(cov) / len(req), res[t]))


if __name__ == "__main__":
    main()
