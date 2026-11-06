#!/usr/bin/env python3
"""Finite matched fake-backend replay for #3731 I005; no product imports."""
import argparse
import hashlib
import itertools
import json
from pathlib import Path

BASE = {"source": "src0", "model": "model0", "imports": "imports0", "proof": "proof0"}
VARIANTS = {
    "proof_edit": {"proof": "proof1"},
    "source_edit": {"source": "src1"},
    "model_change": {"model": "model1"},
    "import_change": {"imports": "imports1"},
}

def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()

def fake_backend(inputs):
    translation = digest({"source": inputs["source"], "model": inputs["model"]})
    proof = digest({"translation": translation, "imports": inputs["imports"], "proof": inputs["proof"]})
    return translation, proof

class Engine:
    def __init__(self, mode):
        self.mode = mode
        self.desired = None
        self.selected = None
        self.requests = {}
        self.translation_cache = set()
        self.proof_cache = set()
        self.calls = {"translation": 0, "proof": 0}
        self.events = []

    def request(self, name, inputs, subscribers):
        self.desired = name
        self.selected = None
        translation, proof = fake_backend(inputs)
        self.requests[name] = {"inputs": dict(inputs), "translation": translation, "proof": proof,
                               "subscribers": set(subscribers), "finished": False}
        if self.mode == "snapshot" or translation not in self.translation_cache:
            self.calls["translation"] += 1
            self.translation_cache.add(translation)
        if self.mode == "snapshot" or proof not in self.proof_cache:
            self.calls["proof"] += 1
            self.proof_cache.add(proof)
        self.record("request_" + name)

    def cancel(self, name, subscriber, cancel_all=False):
        request = self.requests[name]
        if cancel_all:
            request["subscribers"].clear()
        else:
            request["subscribers"].discard(subscriber)
        if self.selected and self.selected["request"] == name:
            if request["subscribers"]:
                self.selected["subscribers"] = sorted(request["subscribers"])
            else:
                self.selected = None
        self.record("cancel_" + subscriber)

    def finish(self, name, fence=True):
        request = self.requests[name]
        request["finished"] = True
        if request["subscribers"] and (not fence or self.desired == name):
            self.selected = {"request": name, "proof_sha256": request["proof"],
                             "input_sha256": digest(request["inputs"]),
                             "subscribers": sorted(request["subscribers"])}
        self.record("finish_" + name)

    def record(self, event):
        selected = dict(self.selected) if self.selected else None
        self.events.append({"event": event, "desired": self.desired, "selected": selected,
                            "current_safe": selected is None or selected["request"] == self.desired})

def schedules():
    for order in itertools.permutations(("edit_B", "cancel_A", "finish_A", "finish_B")):
        if order.index("edit_B") < order.index("finish_B"):
            yield order

def run_edit(variant, order, mode, fence=True):
    engine = Engine(mode)
    engine.request("A", BASE, ("reader_A",))
    changed = dict(BASE, **VARIANTS[variant])
    for event in order:
        if event == "edit_B":
            engine.request("B", changed, ("reader_B",))
        elif event == "cancel_A":
            engine.cancel("A", "reader_A")
        elif event == "finish_A":
            engine.finish("A", fence=fence)
        elif event == "finish_B":
            engine.finish("B", fence=fence)
    if fence:
        assert engine.selected and engine.selected["request"] == "B"
        assert engine.selected["proof_sha256"] == fake_backend(changed)[1]
    return {"order": list(order), "events": engine.events, "calls": engine.calls,
            "stale_publication": any(not item["current_safe"] for item in engine.events)}

def run_shared(order, mode, cancel_all=False):
    engine = Engine(mode)
    engine.request("A", BASE, ("reader_1", "reader_2"))
    for event in order:
        if event == "cancel_1":
            engine.cancel("A", "reader_1", cancel_all=cancel_all)
        else:
            engine.finish("A")
    success = bool(engine.selected and engine.selected["request"] == "A"
                   and engine.selected["subscribers"] == ["reader_2"])
    return {"order": list(order), "events": engine.events, "success_for_survivor": success}

def build():
    result = {"model": "finite fake backends; stage completion delayed by schedule",
              "base_inputs": BASE, "variants": VARIANTS, "cases": {}, "shared_cancel": {}}
    for variant in VARIANTS:
        cases = []
        for order in schedules():
            snapshot = run_edit(variant, order, "snapshot")
            scheduler = run_edit(variant, order, "scheduler")
            unfenced = run_edit(variant, order, "snapshot", fence=False)
            assert [event["selected"] for event in snapshot["events"]] == [event["selected"] for event in scheduler["events"]]
            cases.append({"order": list(order), "snapshot": snapshot,
                          "scheduler": scheduler, "unfenced": unfenced})
        assert len(cases) == 12
        assert all(not case["snapshot"]["stale_publication"] and
                   not case["scheduler"]["stale_publication"] for case in cases)
        result["cases"][variant] = {"schedules": cases,
                                    "unfenced_stale_schedule_count": sum(case["unfenced"]["stale_publication"] for case in cases),
                                    "snapshot_calls": cases[0]["snapshot"]["calls"],
                                    "scheduler_calls": cases[0]["scheduler"]["calls"]}
    for order in itertools.permutations(("cancel_1", "finish_A")):
        key = ",".join(order)
        result["shared_cancel"][key] = {
            "snapshot": run_shared(order, "snapshot"),
            "scheduler": run_shared(order, "scheduler"),
            "cancel_all_negative": run_shared(order, "snapshot", cancel_all=True),
        }
    assert all(case[mode]["success_for_survivor"] for case in result["shared_cancel"].values()
               for mode in ("snapshot", "scheduler"))
    assert all(not case["cancel_all_negative"]["success_for_survivor"] for case in result["shared_cancel"].values())
    result["summary"] = {
        "matched_edit_schedules": sum(len(case["schedules"]) for case in result["cases"].values()),
        "safe_snapshot_schedules": 48,
        "safe_scheduler_schedules": 48,
        "unfenced_stale_schedules": sum(case["unfenced_stale_schedule_count"] for case in result["cases"].values()),
        "shared_cancellation_orders": len(result["shared_cancel"]),
        "both_models_preserve_surviving_reader": True,
        "cancel_all_negative_loses_surviving_reader": True,
    }
    return result

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    parser.add_argument("--check", type=Path)
    args = parser.parse_args()
    result = build()
    encoded = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        assert args.check.read_text() == encoded
        print("PASS: retained I005 result equals fresh finite replay")
    elif args.output:
        args.output.write_text(encoded)
        print(json.dumps(result["summary"], sort_keys=True))
    else:
        print(encoded)
