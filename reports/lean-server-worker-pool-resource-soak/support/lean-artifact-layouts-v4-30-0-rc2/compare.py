#!/usr/bin/env python3
"""Check the two runs agree on structural outcomes and emit timing ranges."""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
summaries = [json.loads((ROOT / name).read_text()) for name in ("summary-run1.json", "summary.json")]
raw = [json.loads((ROOT / name).read_text()) for name in ("raw-run1.json", "raw.json")]
keys = {(c["size"], c["layout"]) for c in summaries[0]["cells"]}
assert len(keys) == 6
assert keys == {(c["size"], c["layout"]) for c in summaries[1]["cells"]}
result = []
for size, layout in sorted(keys):
    cells = [next(c for c in s["cells"] if c["size"] == size and c["layout"] == layout)
             for s in summaries]
    inventories = [next(e["before"] for e in events if e["kind"] == "incremental_inventory"
                        and e["size"] == size and e["layout"] == layout) for events in raw]
    assert set(inventories[0]) == set(inventories[1])
    assert all(inventories[0][k]["sha256"] == inventories[1][k]["sha256"] for k in inventories[0])
    for key in ("module_count", "worker_count", "changed_modules_after_one_proof_edit",
                "failure_rc", "sibling_batch_rc_after_failure", "olean_bytes"):
        assert cells[0][key] == cells[1][key], (size, layout, key)
    metrics = ("cold_ms", "warm_ms", "incremental_ms", "aggregate_import_ms",
               "proof_batch_total_ms", "summed_rss_bytes")
    result.append({"size": size, "layout": layout,
                   "matched_artifact_hashes": True,
                   "module_count": cells[0]["module_count"],
                   "worker_count": cells[0]["worker_count"],
                   "changed_modules_after_one_proof_edit": cells[0]["changed_modules_after_one_proof_edit"],
                   "sibling_batch_rc_after_failure": cells[0]["sibling_batch_rc_after_failure"],
                   "ranges": {k: [min(c[k] for c in cells), max(c[k] for c in cells)]
                              for k in metrics}})
(ROOT / "comparison.json").write_text(json.dumps({"runs": 2, "cells": result}, indent=2,
                                             sort_keys=True) + "\n")
print(json.dumps({"runs": 2, "cells": len(result), "matched_artifact_hashes": True}))
