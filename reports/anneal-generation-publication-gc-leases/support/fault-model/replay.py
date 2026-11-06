#!/usr/bin/env python3
"""Replay a selected stale-completion schedule with the existing fake backend."""
import hashlib
import json
from pathlib import Path
import runpy
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent
HARNESS = ROOT.parent.parent / "anneal-3730-snapshot-capture-jobs-2026-09-29" / "support" / "probe.py"


def sha(value):
    return hashlib.sha256(value.encode()).hexdigest()


def main():
    # runpy executes the existing source without writing its package. Its
    # start_stage launches that same file in backend mode for each real child.
    ns = runpy.run_path(str(HARNESS))
    engine = ns["Engine"]()
    events = []
    semantic_a = {"subject": "fixture-cargo-subject", "source": sha("source-A"),
                  "model": sha("model-A"), "imports": sha("imports-A"),
                  "proof": sha("proof-A")}
    semantic_b = dict(semantic_a, source=sha("source-B"), model=sha("model-B"))
    with tempfile.TemporaryDirectory(prefix="fake-stage-replay-", dir=ROOT) as tmp:
        work = Path(tmp)
        old_request = engine.begin(semantic_a, {"agent"})
        old_job = ns["start_stage"](work, "old", old_request)
        events.append({"event": "old_started_and_gated", "epoch": old_request["epoch"],
                       "pid": old_job["proc"].pid,
                       "request_sha256": sha(json.dumps(old_request, sort_keys=True))})
        new_request = engine.begin(semantic_b, {"agent"})
        new_job = ns["start_stage"](work, "new", new_request)
        events.append({"event": "new_started_and_gated", "epoch": new_request["epoch"],
                       "pid": new_job["proc"].pid,
                       "request_sha256": sha(json.dumps(new_request, sort_keys=True))})
        new_event, new_parsed, new_status = ns["finish_stage"](new_job)
        new_disposition = engine.accept(new_parsed, new_status)
        events.append({"event": "new_completed_first", "backend": new_event,
                       "adapter_status": new_status, "disposition": new_disposition,
                       "selected_epoch": engine.published["request"]["epoch"]})
        old_event, old_parsed, old_status = ns["finish_stage"](old_job)
        old_disposition = engine.accept(old_parsed, old_status)
        events.append({"event": "old_completed_late", "backend": old_event,
                       "adapter_status": old_status, "disposition": old_disposition,
                       "selected_epoch": engine.published["request"]["epoch"]})
        assert new_disposition == "published"
        assert old_disposition == "stale-generation"
        assert engine.published == new_parsed
        assert old_parsed["semantic_digest"] != new_parsed["semantic_digest"]
        outcome = {"harness_sha256": hashlib.sha256(HARNESS.read_bytes()).hexdigest(),
                   "replay_script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                   "python": sys.version, "events": events,
                   "new_digest": new_parsed["semantic_digest"],
                   "old_digest": old_parsed["semantic_digest"],
                   "selected_digest": engine.published["semantic_digest"],
                   "naive_last_completion_digest": old_parsed["semantic_digest"],
                   "late_old_rejected": old_disposition == "stale-generation"}
    (ROOT / "replay-results.json").write_text(json.dumps(outcome, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"late_old_rejected": outcome["late_old_rejected"],
                      "new_digest": outcome["new_digest"], "old_digest": outcome["old_digest"]}))


if __name__ == "__main__":
    main()
