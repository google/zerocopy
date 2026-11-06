#!/usr/bin/env python3
"""Assert and condense the six-cell layout transcript."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
events = json.loads((ROOT / "raw.json").read_text())
semantic = json.loads((ROOT / "semantic-results.json").read_text())
cells = [e for e in events if e["kind"] == "cell"]
assert len(cells) == 6 and not any(e["kind"] == "fatal" for e in events)
assert sum(e["kind"] == "server_exit" and e["rc"] == 0 for e in events) == 6
assert all(e["summed_rss_bytes"] == 0 for e in events
           if e["kind"] == "processes" and e["label"].endswith("-stopped"))
assert [e["rc"] for e in semantic["events"] if e["label"] in
        ("without-import", "with-import", "combined")] == [1, 0, 0]

out = []
for cell in cells:
    size, layout = cell["size"], cell["layout"]
    prefix = f"{size}-{layout}"
    inv = next(e for e in events if e["kind"] == "incremental_inventory" and
               e["size"] == size and e["layout"] == layout)
    proof = [e for e in events if e["kind"] == "command" and
             e["label"].startswith(prefix + "-batch-")]
    assert all(e["rc"] == 0 for e in proof)
    before, after = inv["before"], inv["after"]
    assert set(before) == set(after)
    unchanged = sorted(k for k in before if k not in cell["changed_mtime_modules"])
    assert all(before[k]["sha256"] == after[k]["sha256"] and
               before[k]["mtime_ns"] == after[k]["mtime_ns"] for k in unchanged)
    expected_changed = ({"Aggregate.olean", "AnnOne.olean"} if layout == "per-annotation"
                        else {"Aggregate.olean", "File.olean"} if layout == "per-file"
                        else {"Aggregate.olean", "Artifact.olean"})
    assert set(cell["changed_mtime_modules"]) == expected_changed
    assert cell["worker_count"] == (2 if layout == "per-annotation" else 1)
    assert cell["sibling_rc"] == (0 if layout == "per-annotation" else None)
    assert cell["failure_rc"] != 0
    out.append({"size": size, "layout": layout, "module_count": cell["module_count"],
                "olean_total_bytes": sum(v["bytes"] for v in before.values()),
                "olean_bytes": {k: v["bytes"] for k, v in before.items()},
                "cold_ms": cell["cold_ms"], "warm_ms": cell["warm_ms"],
                "incremental_ms": cell["incremental_ms"],
                "proof_batch_ms": [e["wall_ms"] for e in proof],
                "proof_batch_total_ms": round(sum(e["wall_ms"] for e in proof), 1),
                "aggregate_import_ms": cell["aggregate_import_ms"],
                "changed_modules_after_one_proof_edit": cell["changed_mtime_modules"],
                "unchanged_modules": unchanged, "failure_rc": cell["failure_rc"],
                "sibling_batch_rc_after_failure": cell["sibling_rc"],
                "worker_count": cell["worker_count"],
                "summed_rss_bytes": cell["summed_rss_bytes"]})

for layout in ("per-annotation", "per-file", "per-artifact"):
    small = next(x for x in out if x["layout"] == layout and x["size"] == 1)
    large = next(x for x in out if x["layout"] == layout and x["size"] == 128)
    assert large["olean_total_bytes"] > small["olean_total_bytes"]
result = {"subject": next(e for e in events if e["kind"] == "subject"),
          "cells": out, "semantic": {"without_import_rc": 1, "with_import_rc": 0,
                                     "same_file_rc": 0},
          "scope": "sequential direct Lean/Lake fixture; sum of per-process RSS, not unique footprint"}
(ROOT / "summary.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
print(json.dumps({"cells": len(out), "server_exits": 6,
                  "largest_rss_bytes": max(c["summed_rss_bytes"] for c in out)}))
