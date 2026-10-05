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

def saved_value():
    text = (root / "Local.lean").read_text()
    match = re.search(r"value := (\d+)", text)
    return match.group(1) if match else None

if mode == "build":
    value = saved_value()
    (root / "build-entered").write_text("entered")
    deadline = time.monotonic() + 5
    while (root / "hold-build").exists():
        if time.monotonic() > deadline:
            sys.exit(2)
        time.sleep(0.01)
    if value is None or (root / "fail-build").exists():
        print("fake dependency compilation failed")
        (root / "build-failed").write_text("failed")
        sys.exit(1)
    (root / "built-value").write_text(value)
    print("fake import closure compiled")
    sys.exit(0)
if mode == "setup":
    header = json.loads(sys.stdin.buffer.read())
    with (root / "headers.jsonl").open("a") as output:
        output.write(json.dumps(header) + "\n")
    print(json.dumps({"plugins": [], "options": {}}))
    sys.exit(0)

value = (root / "built-value").read_text() if (root / "built-value").exists() else "0"
lock = threading.Lock()
documents = {}
notifications = []

def send(message):
    data = json.dumps(message).encode()
    with lock:
        sys.stdout.buffer.write(f"Content-Length: {len(data)}\r\n\r\n".encode() + data)
        sys.stdout.buffer.flush()

def diagnostics(uri, version, text):
    errors = []
    if "middle = 10" in text and value != "10":
        errors.append({"message": f"current fake imported value is {value}", "severity": 1,
                       "range": {"start": {"line": 1, "character": 0},
                                 "end": {"line": 1, "character": 1}}})
    send({"jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
          "params": {"uri": uri, "version": version, "isIncremental": False,
                     "diagnostics": errors}})

def delayed_goal(identifier):
    (root / "goal-entered").write_text("entered")
    time.sleep(0.3)
    send({"jsonrpc": "2.0", "id": identifier, "result": {"goals": [f"old value {value}"]}})

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
        send({"jsonrpc": "2.0", "id": message["id"],
              "result": {"capabilities": {"textDocumentSync": 2}}})
    elif method == "$/test/sessionState":
        send({"jsonrpc": "2.0", "id": message["id"], "result": notifications})
    elif method == "textDocument/didOpen":
        doc = message["params"]["textDocument"]
        documents[doc["uri"]] = doc
        with (root / "replays.jsonl").open("a") as output:
            output.write(json.dumps(doc) + "\n")
        diagnostics(doc["uri"], doc["version"], doc["text"])
    elif method == "textDocument/didChange":
        doc = message["params"]["textDocument"]
        # This peer accepts full-text tests; production incremental UTF-16
        # replay is separately exercised by the Rust edit regression.
        text = message["params"]["contentChanges"][-1]["text"]
        documents[doc["uri"]] = {**doc, "text": text}
        diagnostics(doc["uri"], doc["version"], text)
    elif method == "textDocument/didClose":
        documents.pop(message["params"]["textDocument"]["uri"], None)
    elif method == "$/lean/plainGoal":
        threading.Thread(target=delayed_goal, args=(message["id"],), daemon=True).start()
    elif method == "shutdown":
        send({"jsonrpc": "2.0", "id": message["id"], "result": None})
    elif method == "exit":
        (root / "graceful-exit").write_text("exit")
        sys.exit(0)
    elif "id" not in message and method != "initialized":
        notifications.append(message)
