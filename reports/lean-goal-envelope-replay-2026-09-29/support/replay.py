#!/usr/bin/env python3
"""Offline client-policy replay of retained Lean wire records; prints canonical JSON."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
URI = "file://$WORK/Proof.lean"
TRANSCRIPT_HASHES = (
    "12514acc62e577ad18cc446a32a28c23ba3fe1be070f279a22649c31f27c27c0",
    "568711ed5a7d758660dccb72a63ef3d6f0d242e286cd44fa8aaab72c8abff25e",
    "00561c961a49f9544ae4b5af181ce84335968582332df88bba68732b5c6ac8f8",
)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def unique(events, predicate):
    hits = [(i, e) for i, e in enumerate(events) if predicate(e)]
    if len(hits) != 1:
        raise ValueError(f"expected exactly one event; found {len(hits)}")
    return hits[0]


def wire(kind, method=None, request_id=None):
    return lambda e: (e["kind"] == kind and
                      (method is None or e.get("message", {}).get("method") == method) and
                      (request_id is None or e.get("message", {}).get("id") == request_id))


def facts(run, sources, hashes):
    path = ROOT / "transcripts" / f"transcript-run{run}.json"
    data = path.read_bytes()
    if digest(data) != TRANSCRIPT_HASHES[run - 1]:
        raise ValueError(f"transcript {run} differs from retained evidence")
    events = json.loads(data)
    if any(a["ns"] > b["ns"] for a, b in zip(events, events[1:])):
        raise ValueError("nonmonotonic transcript")
    subject = unique(events, lambda e: e["kind"] == "subject")[1]
    if (subject["v1_sha256"], subject["v2_sha256"]) != (hashes["V1"], hashes["V2"]):
        raise ValueError("source hash mismatch")
    opened_i, opened = unique(events, wire("client", "textDocument/didOpen"))
    old_i, old = unique(events, wire("client", "$/lean/plainGoal", 20))
    edit_i, edit = unique(events, wire("client", "textDocument/didChange"))
    wait_i, _ = unique(events, wire("server", request_id=11))
    new_i, new = unique(events, wire("client", "$/lean/plainGoal", 21))
    new_reply_i, new_reply = unique(events, wire("server", request_id=21))
    release_i, _ = unique(events, lambda e: e["kind"] == "v1_released")
    old_reply_i, old_reply = unique(events, wire("server", request_id=20))
    opened_doc = opened["message"]["params"]["textDocument"]
    edited_doc = edit["message"]["params"]["textDocument"]
    if not (opened_i < old_i < edit_i < wait_i < new_i < new_reply_i < release_i < old_reply_i):
        raise ValueError("cross-version barrier order changed")
    if not (opened_doc["uri"] == edited_doc["uri"] == URI and
            opened_doc["version"] == 1 and edited_doc["version"] == 2 and
            opened_doc["text"] == sources["V1"] and
            edit["message"]["params"]["contentChanges"] == [{"text": sources["V2"]}]):
        raise ValueError("open or edit differs from retained sources")
    old_params, new_params = (x["message"]["params"] for x in (old, new))
    if not (old_params["textDocument"]["uri"] == URI and
            new_params["textDocument"]["uri"] == URI and
            new_params["textDocument"].get("version") == 1 and
            old_params["position"] == new_params["position"] and
            new_reply["message"]["result"]["goals"] == ["⊢ False"] and
            old_reply["message"]["result"]["goals"] == ["⊢ True"]):
        raise ValueError("goal request/reply differs from retained evidence")
    return {"position": old_params["position"],
            "old_goal": old_reply["message"]["result"]["goals"][0],
            "new_goal": new_reply["message"]["result"]["goals"][0]}


class Client:
    def __init__(self, source_hash, position):
        self.current = ("A", URI, 1, source_hash, tuple(sorted(position.items())))
        self.pending = {}
        self.accepted = {}

    def submit(self, request_id, historical=False):
        key = (self.current[0], request_id)
        if key in self.pending:
            raise ValueError("duplicate live request")
        self.pending[key] = (self.current, historical)

    def edit(self, version, source_hash):
        incarnation, uri, _, _, position = self.current
        self.current = (incarnation, uri, version, source_hash, position)

    def restart(self, incarnation, version, source_hash):
        _, uri, _, _, position = self.current
        self.current = (incarnation, uri, version, source_hash, position)

    def retarget(self, line, character):
        incarnation, uri, version, source_hash, _ = self.current
        self.current = (incarnation, uri, version, source_hash,
                        tuple(sorted({"line": line, "character": character}.items())))

    def switch_uri(self, uri):
        incarnation, _, version, source_hash, position = self.current
        self.current = (incarnation, uri, version, source_hash, position)

    def receive(self, incarnation, request_id, goal):
        key = (incarnation, request_id)  # The transport supplies incarnation.
        if key not in self.pending:
            return "unknown_request"
        envelope, historical = self.pending.pop(key)
        if incarnation != self.current[0]:
            return "expired_incarnation"
        if historical:
            self.accepted[key] = (envelope, goal, "historical")
            return "historical_only"
        if envelope != self.current:
            return "stale_snapshot"
        self.accepted[key] = (envelope, goal, "latest")
        return "current_live"

    def final_latest(self):
        return [goal for envelope, goal, role in self.accepted.values()
                if role == "latest" and envelope == self.current]


def replay_case(actions, hashes, position, goals):
    client = Client(hashes["V1"], position)
    outcomes = []
    for action in actions:
        op = action[0]
        if op == "submit":
            client.submit(action[1], len(action) > 2 and action[2] == "historical")
        elif op == "edit":
            client.edit(action[1], hashes[action[2]])
        elif op == "restart":
            client.restart(action[1], action[2], hashes[action[3]])
        elif op == "retarget":
            client.retarget(action[1], action[2])
        elif op == "switch_uri":
            client.switch_uri(action[1])
        elif op == "reply":
            outcomes.append({"request": action[2], "goal": goals[action[2]],
                             "decision": client.receive(action[1], action[2], goals[action[2]])})
        else:
            raise ValueError(op)
    return {"replies": outcomes, "final_latest": client.final_latest()}


def main():
    sources = {label: (ROOT / "sources" / f"{label}.lean").read_text()
               for label in ("V1", "V2")}
    hashes = {label: digest(source.encode()) for label, source in sources.items()}
    scenarios = json.loads((ROOT / "scenarios.json").read_text())
    output = {"source_sha256": hashes, "runs": []}
    for run in (1, 2, 3):
        observed = facts(run, sources, hashes)
        cases = {name: replay_case(actions, hashes, observed["position"],
                                   {20: observed["old_goal"], 21: observed["new_goal"]})
                 for name, actions in scenarios.items()}
        output["runs"].append({"run": run, "position": observed["position"], "cases": cases})
    print(json.dumps(output, ensure_ascii=False, sort_keys=True, indent=2))


if __name__ == "__main__":
    main()
