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
import pathlib
import re
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
    local = any(target in ("+Local:olean", "+Middle:olean") for target in targets)
    independent = "+Other:olean" in targets
    value = saved_value() if local else "10"
    other = saved_value("Other", "other") if independent else "10"
    (root / "build-entered").write_text("entered")
    deadline = time.monotonic() + 5
    while (root / "hold-build").exists():
        if time.monotonic() > deadline:
            sys.exit(2)
        time.sleep(0.01)
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
    time.sleep(0.3)
    current = other if "other = 10" in documents.get(uri, {}).get("text", "") else value
    send({"jsonrpc": "2.0", "id": identifier, "result": {"goals": [f"old value {current}"]}})

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
    elif method == "$/test/documentState":
        uri = message["params"]["textDocument"]["uri"]
        send({"jsonrpc": "2.0", "id": message["id"], "result": documents.get(uri)})
    elif method == "initialized":
        (root / "initialized-entered").write_text("entered")
    elif method == "textDocument/didOpen":
        doc = message["params"]["textDocument"]
        documents[doc["uri"]] = doc
        if pathlib.Path(doc["uri"]).name == "Local.lean":
            record_local_version(doc["version"])
        with (root / "replays.jsonl").open("a") as output:
            output.write(json.dumps(doc) + "\n")
        diagnostics(doc["uri"], doc["version"], doc["text"])
    elif method == "textDocument/didChange":
        doc = message["params"]["textDocument"]
        # This peer accepts full-text tests; production incremental UTF-16
        # replay is separately exercised by the Rust edit regression.
        text = message["params"]["contentChanges"][-1]["text"]
        documents[doc["uri"]] = {**doc, "text": text}
        if pathlib.Path(doc["uri"]).name == "Local.lean":
            record_local_version(doc["version"])
        diagnostics(doc["uri"], doc["version"], text)
    elif method == "textDocument/didClose":
        uri = message["params"]["textDocument"]["uri"]
        doc = documents.pop(uri, None)
        if doc is not None:
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
        send({"jsonrpc": "2.0", "id": message["id"], "result": None})
    elif method == "exit":
        (root / "graceful-exit").write_text("exit")
        sys.exit(0)
    elif "id" not in message and method != "initialized":
        notifications.append(message)
