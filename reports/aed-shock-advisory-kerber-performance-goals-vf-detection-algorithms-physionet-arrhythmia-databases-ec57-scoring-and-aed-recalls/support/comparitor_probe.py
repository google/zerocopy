#!/usr/bin/env python3
"""Run wfdb-python's annotation comparator (src/wfdb/processing/evaluate.py at
MIT-LCP/wfdb-python cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e) unmodified on the
same synthetic beat timelines used for the bxb probe.

evaluate.py imports rdann/rdsamp/get_record_list from wfdb.io at module load;
those functions are not used by Comparitor, so this script supplies inert
stand-ins for them and imports the unmodified evaluate.py file. numpy is the
only third-party dependency exercised.

Usage:
  curl -sSfL https://raw.githubusercontent.com/MIT-LCP/wfdb-python/cc9f94fcc8bc938c6fb6cb40fb61c85b33e9404e/src/wfdb/processing/evaluate.py -o evaluate.py
  python3 comparitor_probe.py evaluate.py BEATS_JSON
where BEATS_JSON is the beats.json written by make_annotations.py.
"""
import hashlib
import json
import os
import sys
import tempfile

import numpy as np


def load_evaluate(path):
    tmp = tempfile.TemporaryDirectory()
    root = tmp.name
    os.makedirs(os.path.join(root, "wfdb", "io"))
    os.makedirs(os.path.join(root, "wfdb", "processing"))
    for rel, body in (
        ("wfdb/__init__.py", ""),
        ("wfdb/io/__init__.py", ""),
        ("wfdb/io/annotation.py", "def rdann(*a, **k):\n    raise NotImplementedError\n"),
        ("wfdb/io/download.py", "def get_record_list(*a, **k):\n    raise NotImplementedError\n"),
        ("wfdb/io/record.py", "def rdsamp(*a, **k):\n    raise NotImplementedError\n"),
        ("wfdb/processing/__init__.py", ""),
    ):
        with open(os.path.join(root, rel), "w") as f:
            f.write(body)
    with open(path, "rb") as f:
        src = f.read()
    with open(os.path.join(root, "wfdb", "processing", "evaluate.py"), "wb") as f:
        f.write(src)
    sys.path.insert(0, root)
    import wfdb.processing.evaluate as ev  # noqa: E402
    return tmp, ev, hashlib.sha256(src).hexdigest()


def main(evaluate_path, beats_json):
    tmp, ev, digest = load_evaluate(evaluate_path)
    print("evaluate.py sha256:", digest)
    print("numpy", np.__version__)
    beats = json.load(open(beats_json))

    win = beats["win"]
    ref = np.array(win["ref"]) 
    test = np.array(win["test"])
    print("record win: offsets cycle", win["offsets"], "(samples at 360 Hz)")
    for w in (36, 54, 55):
        c = ev.compare_annotations(ref, test, w)
        matched_offsets = sorted({int(test[c.matching_sample_nums[i]] - ref[i])
                                  for i in range(len(ref)) if c.matching_sample_nums[i] != -1})
        print("  window_width=%d: tp=%d fp=%d fn=%d Se=%.4f +P=%.4f matched offsets=%s" % (
            w, c.tp, c.fp, c.fn, c.sensitivity, c.positive_predictivity, matched_offsets))
    print("  note: int(0.1*360) =", int(0.1 * 360), "(window used by benchmark_mitdb)")

    # Aggregation: benchmark_mitdb averages per-record statistics with np.mean.
    comps = []
    for rec in ("agA", "agB"):
        r = np.array(beats[rec]["ref"]) 
        t = np.array(beats[rec]["test"]) 
        c = ev.compare_annotations(r, t, 54)
        comps.append(c)
        print("record %s: tp=%d fn=%d Se=%.4f" % (rec, c.tp, c.fn, c.sensitivity))
    mean_se = np.mean([c.sensitivity for c in comps])
    gross_se = sum(c.tp for c in comps) / sum(c.tp + c.fn for c in comps)
    print("per-record mean Se (as in benchmark_mitdb) = %.4f; gross Se = %.4f" % (mean_se, gross_se))
    tmp.cleanup()


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
