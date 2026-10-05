#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Tiny private protocol peer for lean_server unit tests. Never invokes Lean."""
import json
import fcntl
import os
import pathlib
import re
import signal
import subprocess
import sys
import threading
import time

root = pathlib.Path(sys.argv[1])
mode = sys.argv[2]
with (root / "calls.jsonl").open("a") as output:
    output.write(json.dumps({"mode": mode, "args": sys.argv[3:]}) + "\n")

def saved_value(module="Local", name="value"):
    text = (root / f"{module}.lean").read_text()
    match = re.search(rf"{name} := (\d+)", text)
    return match.group(1) if match else None

if mode == "build":
    targets = sys.argv[3:]
    declared = root / "declared-targets"
    forbidden = root / "fail-build-targets"
    if (declared.exists() and any(target not in declared.read_text().splitlines()
                                  for target in targets)) or (
            forbidden.exists() and any(target in forbidden.read_text().splitlines()
                                       for target in targets)):
        (root / "build-failed").write_text("failed")
        sys.exit(1)
    local = any(target in ("+Local:olean", "+Middle:olean") for target in targets)
    independent = "+Other:olean" in targets
    value = saved_value() if local else "10"
    other = saved_value("Other", "other") if independent else "10"
    (root / "build-entered").write_text("entered")
    with (root / "build-generations.jsonl").open("a") as output:
        output.write(json.dumps({"value": value, "pid": os.getpid()}) + "\n")
    # The locks describe actual process lifetimes, including forced SIGKILL.
    # A SIGTERM callback marker only describes how far its handler ran.
    lifetime = (root / f"build-lifetime-{value}").open("w")
    fcntl.flock(lifetime, fcntl.LOCK_EX)
    ignore_term = (root / "ignore-build-term").exists()
    emergency_hold_seconds = 20 if (root / "hold-build-cancel-required").exists() else 5
    child = None
    if (root / "spawn-build-child").exists():
        child = subprocess.Popen([sys.executable, "-I", "-B", "-c",
            "import fcntl,pathlib,signal,sys,time; "
            "p=pathlib.Path(sys.argv[1]); "
            "lifetime=open(sys.argv[3],'w'); fcntl.flock(lifetime,fcntl.LOCK_EX); "
            "signal.signal(signal.SIGTERM,signal.SIG_IGN if sys.argv[4]=='ignore' "
            "else lambda *_:(p.write_text('stopped'),sys.exit(0))); "
            "pathlib.Path(sys.argv[2]).write_text('ready'); time.sleep(float(sys.argv[5]))",
            str(root / f"child-stopped-{value}"), str(root / f"child-ready-{value}"),
            str(root / f"child-lifetime-{value}"), "ignore" if ignore_term else "graceful",
            str(emergency_hold_seconds)])

    def stop_build(*_):
        if child is not None:
            try:
                child.wait(timeout=0.2)
            except subprocess.TimeoutExpired:
                child.kill()
                child.wait()
        (root / f"build-stopped-{value}").write_text("stopped")
        sys.exit(143)

    signal.signal(signal.SIGTERM, signal.SIG_IGN if ignore_term else stop_build)
    # Cancellation oracles can request a longer emergency timeout so their
    # bounded lifetime checks cannot be satisfied by this natural exit.
    deadline = time.monotonic() + emergency_hold_seconds
    while ((root / "hold-build").exists()
           or ((root / "hold-build-value").exists()
               and (root / "hold-build-value").read_text().strip() == value)):
        (root / f"build-held-{value}").write_text("held")
        if time.monotonic() > deadline:
            sys.exit(2)
        time.sleep(0.01)
    if value == "30" and (root / "spawn-build-child").exists():
        def lifetime_released(name):
            deadline = time.monotonic() + 0.25
            with (root / name).open("r+") as handle:
                while True:
                    try:
                        fcntl.flock(handle, fcntl.LOCK_EX | fcntl.LOCK_NB)
                        return True
                    except BlockingIOError:
                        if time.monotonic() >= deadline:
                            return False
                        time.sleep(0.01)

        (root / "replacement-saw-cleanup").write_text(json.dumps({
            "parent": lifetime_released("build-lifetime-20"),
            "child": lifetime_released("child-lifetime-20")}))
    if child is not None:
        child.terminate()
        child.wait(timeout=1)
    if value is None or other is None or (root / "fail-build").exists():
        print("fake dependency compilation failed")
        (root / "build-failed").write_text("failed")
        sys.exit(1)
    if local:
        (root / "built-value").write_text(value)
    if independent:
        (root / "built-other-value").write_text(other)
    if (root / "race-build-finish").exists():
        (root / "race-build-finish").unlink()
        (root / "stamp-races").write_text("3")
    print("fake import closure compiled")
    sys.exit(0)
if mode == "setup":
    header = json.loads(sys.stdin.buffer.read())
    with (root / "headers.jsonl").open("a") as output:
        output.write(json.dumps(header) + "\n")
    print(json.dumps({"plugins": [], "options": {}}))
    sys.exit(0)

value = (root / "built-value").read_text() if (root / "built-value").exists() else "0"
other = (root / "built-other-value").read_text() if (root / "built-other-value").exists() else "0"
lock = threading.Lock()
documents = {}
notifications = []
watched_events = 0
watcher_replies = 0
finalized = {}
pending_ileans = []
cancelled = set()
pending_configuration = None
pending_shutdown = None
pending_apply_edit = None

def send(message):
    data = json.dumps(message).encode()
    with lock:
        sys.stdout.buffer.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        sys.stdout.buffer.flush()

def record_local_version(version):
    pending = root / "last-local-version.tmp"
    pending.write_text(str(version))
    pending.replace(root / "last-local-version")

def diagnostics(uri, version, text):
    errors = []
    if (root / "missing-foo").exists() and re.search(r"(?m)^import (?:src\.)?Foo\b", text):
        errors.append({"message": "fake unresolved module Foo", "severity": 1,
                       "range": {"start": {"line": 0, "character": 0},
                                 "end": {"line": 0, "character": 1}}})
    if "value := broken" in text:
        errors.append({"message": "fake local source parse error", "severity": 1,
                       "range": {"start": {"line": 0, "character": 0},
                                 "end": {"line": 0, "character": 1}}})
    if "other = 10" in text and other != "10":
        errors.append({"message": f"current fake independent value is {other}", "severity": 1,
                       "range": {"start": {"line": 1, "character": 0},
                                 "end": {"line": 1, "character": 1}}})
    if ("middle = 10" in text or "value = 10" in text) and value != "10":
        errors.append({"message": f"current fake imported value is {value}", "severity": 1,
                       "range": {"start": {"line": 1, "character": 0},
                                 "end": {"line": 1, "character": 1}}})
    send({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
          "params": {"uri": uri, "version": version, "isIncremental": False,
                     "diagnostics": errors}})

def delayed_goal(identifier, uri):
    (root / "goal-entered").write_text("entered")
    deadline = time.monotonic() + 5
    while (root / "hold-goal").exists():
        if time.monotonic() > deadline:
            return
        time.sleep(0.01)
    time.sleep(0.3)
    current = other if "other = 10" in documents.get(uri, {}).get("text", "") else value
    send({"jsonrpc": "2.0", "id": identifier, "result": {"goals": [f"old value {current}"]}})
    (root / "goal-completed").write_text("completed")

def finalize(uri, version):
    finalized[uri] = version
    # Match RC2's watchdog hazard: every waiter for this URI is removed,
    # including one whose future target has not yet finalized.
    selected = [wait for wait in pending_ileans if wait[1] == uri]
    pending_ileans[:] = [wait for wait in pending_ileans if wait[1] != uri]
    for identifier, _, minimum in selected:
        if minimum <= version:
            send({"jsonrpc": "2.0", "id": identifier, "result": {}})

def wait_diagnostics(identifier, uri, minimum, captured):
    # Match RC2's captured immutable RequestContext.doc: forwarding a future
    # target early cannot observe the subsequent didChange.
    if captured.get("version", -1) < minimum:
        return
    finalize(uri, captured["version"] - 1)
    (root / "older-finalization").write_text(str(captured["version"] - 1))
    (root / "diagnostics-wait-entered").write_text("entered")
    deadline = time.monotonic() + 5
    while (root / "hold-diagnostics-wait").exists():
        if time.monotonic() > deadline or identifier in cancelled:
            return
        time.sleep(0.01)
    if identifier in cancelled:
        return
    diagnostics(uri, captured["version"], captured.get("text", ""))
    finalize(uri, captured["version"])
    send({"jsonrpc": "2.0", "id": identifier, "result": {}})

while True:
    length = None
    while True:
        line = sys.stdin.buffer.readline()
        if not line:
            sys.exit(0)
        if line in (b"\r\n", b"\n"):
            break
        key, _, val = line.partition(b":")
        if key.lower() == b"content-length":
            length = int(val.strip())
    message = json.loads(sys.stdin.buffer.read(length))
    method = message.get("method")
    if method == "initialize":
        if (root / "hold-initialize").exists():
            (root / "initialize-entered").write_text("entered")
            deadline = time.monotonic() + 5
            while (root / "hold-initialize").exists():
                if time.monotonic() > deadline:
                    sys.exit(2)
                time.sleep(0.01)
        if (root / "race-initialize-result").exists():
            (root / "race-initialize-result").unlink()
            (root / "stamp-races").write_text("3")
        send({"jsonrpc": "2.0", "id": message["id"],
              "result": {"capabilities": {"textDocumentSync": 2}}})
    elif method == "$/test/sessionState":
        send({"jsonrpc": "2.0", "id": message["id"], "result": notifications})
    elif method == "$/test/watchedEventCount":
        send({"jsonrpc": "2.0", "id": message["id"], "result": watched_events})
    elif method == "$/test/watcherReplyCount":
        send({"jsonrpc": "2.0", "id": message["id"], "result": watcher_replies})
    elif method == "$/test/documentState":
        uri = message["params"]["textDocument"]["uri"]
        send({"jsonrpc": "2.0", "id": message["id"], "result": documents.get(uri)})
    elif method == "$/test/requestConfiguration":
        if (root / "hold-configuration").exists():
            (root / "configuration-entered").write_text("entered")
            deadline = time.monotonic() + 3
            while (root / "hold-configuration").exists():
                if time.monotonic() > deadline:
                    sys.exit(2)
                time.sleep(0.01)
        pending_configuration = "fake-configuration"
        send({"jsonrpc": "2.0", "id": pending_configuration,
              "method": "workspace/configuration", "params": {"items": []}})
        send({"jsonrpc": "2.0", "id": message["id"], "result": None})
    elif method is None and message.get("id") == pending_configuration:
        pending_configuration = None
        (root / "configuration-replied").write_text("replied")
        if pending_shutdown is not None:
            send({"jsonrpc": "2.0", "id": pending_shutdown, "result": None})
            pending_shutdown = None
    elif method is None and message.get("id") == pending_apply_edit:
        pending_apply_edit = None
        (root / "apply-edit-replied").write_text(json.dumps(message))
    elif method in ("textDocument/waitForDiagnostics", "$/lean/waitForILeans"):
        uri = message["params"]["uri"]
        minimum = message["params"]["version"]
        captured = dict(documents.get(uri, {}))
        with (root / "waits.jsonl").open("a") as output:
            output.write(json.dumps({"method": method, "minimum": minimum,
                "captured": captured.get("version"), "finalized": finalized.get(uri)}) + "\n")
        if method == "textDocument/waitForDiagnostics":
            threading.Thread(target=wait_diagnostics,
                args=(message["id"], uri, minimum, captured), daemon=True).start()
        elif finalized.get(uri, -1) >= minimum:
            send({"jsonrpc": "2.0", "id": message["id"], "result": {}})
        else:
            pending_ileans.append((message["id"], uri, minimum))
    elif method == "$/cancelRequest":
        identifier = message["params"]["id"]
        cancelled.add(identifier)
        send({"jsonrpc": "2.0", "id": identifier,
              "error": {"code": -32800, "message": "fake request cancelled"}})
    elif method == "initialized":
        (root / "initialized-entered").write_text("entered")
        if (root / "emit-watcher-registration").exists():
            with (root / "watcher-requests.jsonl").open("a") as output:
                output.write(json.dumps({"pid": os.getpid()}) + "\n")
            send({"jsonrpc": "2.0", "id": "register_lean_watcher",
                  "method": "client/registerCapability", "params": {"registrations": [{
                      "id": "lean_watcher", "method": "workspace/didChangeWatchedFiles",
                      "registerOptions": {"watchers": [
                          {"globPattern": "**/*.lean"}, {"globPattern": "**/*.ilean"}]}}]}})
    elif method == "textDocument/didOpen":
        doc = message["params"]["textDocument"]
        documents[doc["uri"]] = doc
        if pathlib.Path(doc["uri"]).name == "Local.lean":
            record_local_version(doc["version"])
        with (root / "replays.jsonl").open("a") as output:
            output.write(json.dumps(doc) + "\n")
        diagnostics(doc["uri"], doc["version"], doc["text"])
        if not (root / "hold-diagnostics-wait").exists():
            finalize(doc["uri"], doc["version"])
    elif method == "textDocument/didChange":
        doc = message["params"]["textDocument"]
        # This peer accepts full-text tests; production incremental UTF-16
        # replay is separately exercised by the Rust edit regression.
        text = message["params"]["contentChanges"][-1]["text"]
        documents[doc["uri"]] = {**doc, "text": text}
        if pathlib.Path(doc["uri"]).name == "Local.lean":
            record_local_version(doc["version"])
        diagnostics(doc["uri"], doc["version"], text)
        if (root / "apply-edit-on-change").exists():
            target = (root / "apply-edit-on-change").read_text()
            (root / "apply-edit-on-change").unlink()
            pending_apply_edit = "fake-apply-edit"
            send({"jsonrpc": "2.0", "id": pending_apply_edit,
                  "method": "workspace/applyEdit", "params": {"edit": {"changes": {
                      target: [{"range": {"start": {"line": 0, "character": 0},
                                         "end": {"line": 0, "character": 0}},
                                "newText": "-- stale edit\\n"}]}}}})
            (root / "apply-edit-emitted").write_text("emitted")
        if not (root / "hold-diagnostics-wait").exists():
            finalize(doc["uri"], doc["version"])
    elif method == "textDocument/didClose":
        uri = message["params"]["textDocument"]["uri"]
        doc = documents.pop(uri, None)
        if doc is not None:
            if (root / "hold-close-clear").exists():
                (root / "close-clear-held").write_text("held")
                continue
            # Exercise obsolete diagnostics both before and after the current
            # close clearing. Neither may survive the closed-document filter.
            diagnostics(uri, doc["version"] + 1, "")
            send({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                  "params": {"uri": uri, "version": doc["version"],
                             "diagnostics": [{"message": "late closed proof result"}]}})
            diagnostics(uri, doc["version"], "")
            send({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                  "params": {"uri": uri, "version": doc["version"],
                             "diagnostics": [{"message": "late closed proof result"}]}})
    elif method == "$/lean/plainGoal":
        threading.Thread(target=delayed_goal, args=(message["id"], message["params"]["textDocument"]["uri"]), daemon=True).start()
    elif method == "shutdown":
        if pending_configuration is not None:
            (root / "shutdown-before-configuration-reply").write_text("waiting")
            pending_shutdown = message["id"]
        else:
            send({"jsonrpc": "2.0", "id": message["id"], "result": None})
    elif method == "exit":
        (root / "graceful-exit").write_text("exit")
        sys.exit(0)
    elif method is None and message.get("id") == "register_lean_watcher":
        watcher_replies += 1
        with (root / "watcher-replies.jsonl").open("a") as output:
            output.write(json.dumps({"pid": os.getpid(), "reply": message}) + "\n")
    elif method == "workspace/didChangeWatchedFiles":
        watched_events += 1
    elif "id" not in message and method != "initialized":
        notifications.append(message)
        if method == "$/test/appendState" and message["params"]["value"] == "during":
            (root / "deferred-during-received").write_text("received")
