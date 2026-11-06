#!/usr/bin/env python3
"""Bounded, serial Lean LSP smoke probe. Does not modify the SDK tree.

Example (prepare the workspace and env file first):

  python3 -B lsp_driver.py --env-file real_sdk_lake.env \
    --workspace /absolute/private/workspace \
    --immutable-root /absolute/installed/aeneas --label native-smoke

The env file is JSON {"KEY":"VALUE"} or literal KEY=VALUE lines. It is data,
not sourced through a shell. All output stays in this task's records directory.
"""

import argparse
import json
import os
import re
import select
import shlex
import signal
import subprocess
import sys
import time
from pathlib import Path
from urllib.parse import unquote, urlparse

from guard import ROOT, host_sample, processes

RECORDS = ROOT / "records"
TRACE = ROOT / "trace.dylib"
RSS_LIMIT_KIB = 3072 * 1024
DISK_FLOOR_BYTES = 10 * 1024**3
STDOUT_CAP = 64 * 1024**2


def env_data(path):
    raw = path.read_text()
    if raw.lstrip().startswith("{"):
        values = json.loads(raw)
        if not isinstance(values, dict):
            raise ValueError("JSON env file must be an object")
        return {str(k): str(v) for k, v in values.items()}
    values = {}
    for number, line in enumerate(raw.splitlines(), 1):
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        if line.startswith("export "):
            line = line[7:].strip()
        key, sep, value = line.partition("=")
        if not sep or not re.fullmatch(r"[A-Za-z_][A-Za-z_0-9]*", key):
            raise ValueError(f"Invalid env assignment at line {number}")
        value = value.strip()
        if value.startswith(("'", '"')):
            words = shlex.split(value)
            if len(words) != 1:
                raise ValueError(f"Invalid quoted value at line {number}")
            value = words[0]
        values[key] = value
    return values


def goal_position(text, override):
    lines = text.splitlines()
    if override is not None:
        if override < 0 or override >= len(lines):
            raise ValueError("--goal-line is outside NativeSmoke.lean")
        return {"line": override, "character": 0}
    for index, line in enumerate(lines):
        if re.match(r"^\s*trivial\b", line) and index > 0:
            if lines[index - 1].strip():
                raise ValueError("Expected a blank line directly before trivial")
            return {"line": index - 1, "character": 0}
    raise ValueError("No trivial tactic found; pass --goal-line explicitly")


def token_position(text, token):
    count = text.count(token)
    if count != 1:
        raise ValueError(f"Expected one {token!r} token, found {count}")
    before = text[:text.index(token)]
    return {"line": before.count("\n"),
            "character": len(before.rsplit("\n", 1)[-1]) + 1}


def definition_source(response, expected):
    if "error" in response:
        raise RuntimeError(f"Definition request failed: {response['error']}")
    locations = response.get("result")
    if locations is None:
        raise RuntimeError("Definition is null; source navigation unsupported")
    if isinstance(locations, dict):
        locations = [locations]
    if not isinstance(locations, list) or not locations:
        raise RuntimeError(f"Definition has no locations: {locations!r}")
    target = expected.resolve(strict=True)
    for location in locations:
        uri = location.get("targetUri", location.get("uri"))
        parsed = urlparse(uri or "")
        if parsed.scheme != "file" or parsed.netloc not in ("", "localhost"):
            continue
        path = Path(unquote(parsed.path)).resolve(strict=True)
        if path == target and path.is_file() and os.access(path, os.R_OK):
            return {"uri": uri, "path": str(path),
                    "range": location.get("targetRange", location.get("range"))}
    raise RuntimeError(f"Definition did not resolve to readable {target}: {locations!r}")


class FramedStream:
    def __init__(self):
        self.buffer = bytearray()

    def add(self, chunk):
        self.buffer.extend(chunk)
        messages = []
        while True:
            end = self.buffer.find(b"\r\n\r\n")
            width = 4
            if end < 0:
                end = self.buffer.find(b"\n\n")
                width = 2
            if end < 0:
                break
            header = bytes(self.buffer[:end]).decode("ascii")
            match = re.search(r"(?im)^Content-Length:\s*(\d+)\s*$", header)
            if not match:
                raise ValueError("LSP frame has no Content-Length")
            size = int(match.group(1))
            if size > 32 * 1024**2:
                raise ValueError("LSP frame exceeds 32 MiB")
            start = end + width
            if len(self.buffer) < start + size:
                break
            body = bytes(self.buffer[start : start + size])
            del self.buffer[: start + size]
            messages.append(json.loads(body))
        return messages


def send(stream, message):
    body = json.dumps(message, separators=(",", ":"), ensure_ascii=False).encode()
    stream.write(b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body)
    stream.flush()


def request(stream, number, method, params=None):
    item = {"jsonrpc": "2.0", "id": number, "method": method}
    if params is not None:
        item["params"] = params
    send(stream, item)


def notify(stream, method, params=None):
    item = {"jsonrpc": "2.0", "method": method}
    if params is not None:
        item["params"] = params
    send(stream, item)


def reply_to_server(stream, message):
    method = message.get("method")
    if method == "workspace/configuration":
        result = [{} for _ in message.get("params", {}).get("items", [])]
    elif method in ("client/registerCapability", "client/unregisterCapability",
                    "window/workDoneProgress/create"):
        result = None
    else:
        send(stream, {"jsonrpc": "2.0", "id": message["id"], "error":
                      {"code": -32601, "message": f"Unsupported client method: {method}"}})
        return
    send(stream, {"jsonrpc": "2.0", "id": message["id"], "result": result})


def safe_stop(child):
    if child is None:
        return
    # Only the session created for this known child is signaled.
    try:
        os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError:
        pass
    if child.poll() is not None:
        return
    try:
        child.wait(timeout=2)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        child.wait(timeout=2)


def run(args):
    workspace = args.workspace.resolve(strict=True)
    source = workspace / "NativeSmoke.lean"
    if not source.is_file():
        raise FileNotFoundError(source)
    text = source.read_text()
    position = goal_position(text, args.goal_line)
    values = env_data(args.env_file.resolve(strict=True))
    env = os.environ.copy()
    env.update(values)
    if args.navigation:
        env.pop("DYLD_PRINT_LIBRARIES", None)
    lean = args.lean or Path(env["LEAN_SYSROOT"]) / "bin/lean"
    lean = lean.resolve(strict=True)
    if not os.access(lean, os.X_OK):
        raise ValueError(f"Lean is not executable: {lean}")
    roots = [p.resolve(strict=True) for p in args.immutable_root]
    if not roots:
        raise ValueError("At least one --immutable-root is required")
    if not TRACE.is_file():
        raise FileNotFoundError(TRACE)

    RECORDS.mkdir(exist_ok=True)
    prefix = RECORDS / args.label
    paths = {name: Path(str(prefix) + suffix) for name, suffix in {
        "stdout": ".lsp.stdout.raw", "stderr": ".lsp.stderr",
        "messages": ".lsp.messages.jsonl", "events": ".lsp.events.jsonl",
        "result": ".lsp.result.json"}.items()}
    for path in paths.values():
        if path.exists():
            raise FileExistsError(f"Refusing to overwrite existing probe: {path}")

    first = host_sample()
    if first["memory_free_pct"] is None or first["memory_free_pct"] < 30:
        raise RuntimeError(f"Host memory admission requires >=30% free: {first}")
    if first["disk_free_bytes"] < DISK_FLOOR_BYTES:
        raise RuntimeError(f"Disk admission requires >=10 GiB free: {first}")
    env["PROBE_IMMUTABLE_ROOTS"] = ":".join(str(p) for p in roots)
    env["PROBE_TRACE_LOG"] = str(paths["events"])
    inserted = env.get("DYLD_INSERT_LIBRARIES", "")
    env["DYLD_INSERT_LIBRARIES"] = ":".join(p for p in (inserted, str(TRACE)) if p)

    uri = source.as_uri()
    root_uri = workspace.as_uri()
    result = {"label": args.label, "cmd": [str(lean), "--server"],
              "workspace": str(workspace), "source": str(source),
              "goal_position": position, "immutable_roots": [str(p) for p in roots],
              "limits": {"admission_memory_free_pct": 30,
                         "host_memory_floor_pct": 25, "rss_mib": 3072,
                         "disk_floor_gib": 10, "timeout_s": args.timeout_s},
              "samples": [], "abort": None, "result": None}
    child = None
    start = time.monotonic()
    previous_host = first
    next_host = 0.0
    stage = "initialize"
    responses = {}
    diagnostics = None
    diagnostic_version = None
    diagnostics_by_version = {}
    goal = None
    definitions = {}
    if args.navigation:
        if args.expected_aeneas_source is None or args.expected_mathlib_source is None:
            raise ValueError("Navigation requires both expected source paths")
        aeneas_position = token_position(text, "aeneas_saturate")
        mathlib_position = token_position(text, "Nat.succ_injective")
        old_proof = "example : True := by"
        if text.count(old_proof) != 1:
            raise ValueError("Expected one True proof to edit in memory")
        false_text = text.replace(old_proof, "example : False := by")
    decoder = FramedStream()
    stdout_bytes = 0

    def interrupt(_signum, _frame):
        raise KeyboardInterrupt("Driver interrupted")

    old_term = signal.signal(signal.SIGTERM, interrupt)
    old_int = signal.signal(signal.SIGINT, interrupt)
    try:
        with paths["stdout"].open("wb") as raw, paths["stderr"].open("wb") as err, \
             paths["messages"].open("w") as messages:
            child = subprocess.Popen([str(lean), "--server"], cwd=workspace,
                                     env=env, stdin=subprocess.PIPE,
                                     stdout=subprocess.PIPE, stderr=err,
                                     start_new_session=True, bufsize=0)
            result["pid"] = child.pid
            Path(str(prefix) + ".lsp.pid").write_text(str(child.pid))
            request(child.stdin, 1, "initialize", {
                "processId": os.getpid(), "rootUri": root_uri,
                "workspaceFolders": [{"uri": root_uri, "name": workspace.name}],
                "capabilities": {"textDocument": {"publishDiagnostics":
                                                  {"relatedInformation": True}}},
                "clientInfo": {"name": "anneal-v1-validation", "version": "1"}})
            os.set_blocking(child.stdout.fileno(), False)
            while True:
                elapsed = time.monotonic() - start
                if elapsed >= next_host:
                    previous_host = host_sample()
                    next_host = elapsed + 1.0
                rows = processes(child.pid)
                sample = {"elapsed_s": round(elapsed, 3),
                          "rss_kib": sum(row["rss_kib"] for row in rows),
                          "processes": rows, **previous_host}
                result["samples"].append(sample)
                reason = None
                if elapsed > args.timeout_s:
                    reason = "timeout"
                elif sample["rss_kib"] > RSS_LIMIT_KIB:
                    reason = "process-group RSS"
                elif sample["memory_free_pct"] is None or sample["memory_free_pct"] < 25:
                    reason = "host memory pressure"
                elif sample["disk_free_bytes"] < DISK_FLOOR_BYTES:
                    reason = "disk floor"
                if reason:
                    result["abort"] = reason
                    raise RuntimeError(f"Guard abort: {reason}")
                if child.poll() is not None and not select.select([child.stdout], [], [], 0)[0]:
                    raise RuntimeError(f"Lean server exited early: {child.returncode}")
                ready, _, _ = select.select([child.stdout], [], [], 0.2)
                if not ready:
                    continue
                chunk = os.read(child.stdout.fileno(), 65536)
                if not chunk:
                    raise RuntimeError("Lean server closed stdout")
                stdout_bytes += len(chunk)
                if stdout_bytes > STDOUT_CAP:
                    raise RuntimeError("LSP stdout exceeded 64 MiB cap")
                raw.write(chunk)
                for message in decoder.add(chunk):
                    messages.write(json.dumps(message, ensure_ascii=False) + "\n")
                    messages.flush()
                    if "id" in message and "method" in message:
                        reply_to_server(child.stdin, message)
                    elif "id" in message:
                        responses[message["id"]] = message
                    elif message.get("method") == "textDocument/publishDiagnostics":
                        params = message.get("params", {})
                        if params.get("uri") == uri:
                            diagnostics = params.get("diagnostics", [])
                            diagnostic_version = params.get("version")
                            if diagnostic_version is not None:
                                diagnostics_by_version[diagnostic_version] = diagnostics

                if stage == "initialize" and 1 in responses:
                    if "error" in responses[1]:
                        raise RuntimeError(f"Initialize rejected: {responses[1]['error']}")
                    notify(child.stdin, "initialized", {})
                    notify(child.stdin, "textDocument/didOpen", {"textDocument": {
                        "uri": uri, "languageId": "lean4", "version": 1, "text": text}})
                    request(child.stdin, 2, "textDocument/waitForDiagnostics",
                            {"uri": uri, "version": 1})
                    stage = "diagnostics"
                if stage == "diagnostics" and 2 in responses and diagnostics is not None:
                    if "error" in responses[2]:
                        raise RuntimeError(f"Diagnostics wait rejected: {responses[2]['error']}")
                    if diagnostic_version is not None and diagnostic_version < 1:
                        continue
                    errors = [d for d in diagnostics if d.get("severity", 1) == 1]
                    if errors:
                        raise RuntimeError(f"NativeSmoke diagnostics contain errors: {errors[:3]}")
                    request(child.stdin, 3, "$/lean/plainGoal", {
                        "textDocument": {"uri": uri}, "position": position})
                    stage = "goal"
                if stage == "goal" and 3 in responses:
                    if "error" in responses[3]:
                        raise RuntimeError(f"Plain-goal request failed: {responses[3]['error']}")
                    goal = responses[3].get("result")
                    if goal is None:
                        raise RuntimeError("Plain goal is null at the blank line before trivial")
                    if args.navigation:
                        request(child.stdin, 4, "textDocument/definition", {
                            "textDocument": {"uri": uri}, "position": aeneas_position})
                        request(child.stdin, 5, "textDocument/definition", {
                            "textDocument": {"uri": uri}, "position": mathlib_position})
                        stage = "definitions"
                    else:
                        request(child.stdin, 9, "shutdown")
                        stage = "shutdown"
                if stage == "definitions" and 4 in responses and 5 in responses:
                    definitions["aeneas"] = definition_source(
                        responses[4], args.expected_aeneas_source)
                    definitions["mathlib"] = definition_source(
                        responses[5], args.expected_mathlib_source)
                    notify(child.stdin, "textDocument/didChange", {
                        "textDocument": {"uri": uri, "version": 2},
                        "contentChanges": [{"text": false_text}]})
                    request(child.stdin, 6, "textDocument/waitForDiagnostics",
                            {"uri": uri, "version": 2})
                    stage = "false-diagnostics"
                if stage == "false-diagnostics" and 6 in responses and 2 in diagnostics_by_version:
                    if "error" in responses[6]:
                        raise RuntimeError(f"False-edit wait rejected: {responses[6]['error']}")
                    errors = [d for d in diagnostics_by_version[2]
                              if d.get("severity", 1) == 1]
                    if not errors:
                        raise RuntimeError("Unsaved False edit produced no error diagnostics")
                    result["false_edit_error_count"] = len(errors)
                    notify(child.stdin, "textDocument/didChange", {
                        "textDocument": {"uri": uri, "version": 3},
                        "contentChanges": [{"text": text}]})
                    request(child.stdin, 7, "textDocument/waitForDiagnostics",
                            {"uri": uri, "version": 3})
                    stage = "restored-diagnostics"
                if stage == "restored-diagnostics" and 7 in responses and 3 in diagnostics_by_version:
                    if "error" in responses[7]:
                        raise RuntimeError(f"Restore wait rejected: {responses[7]['error']}")
                    errors = [d for d in diagnostics_by_version[3]
                              if d.get("severity", 1) == 1]
                    if errors:
                        raise RuntimeError(f"Restored True proof has errors: {errors[:3]}")
                    request(child.stdin, 8, "$/lean/plainGoal", {
                        "textDocument": {"uri": uri}, "position": position})
                    stage = "restored-goal"
                if stage == "restored-goal" and 8 in responses:
                    if "error" in responses[8] or responses[8].get("result") is None:
                        raise RuntimeError(f"Restored plain goal unavailable: {responses[8]}")
                    result["restored_goal"] = responses[8]["result"]
                    request(child.stdin, 9, "shutdown")
                    stage = "shutdown"
                if stage == "shutdown" and 9 in responses:
                    if "error" in responses[9]:
                        raise RuntimeError(f"Shutdown rejected: {responses[9]['error']}")
                    notify(child.stdin, "exit")
                    child.stdin.close()
                    try:
                        child.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        raise RuntimeError("Server did not exit after shutdown")
                    if child.returncode != 0:
                        raise RuntimeError(f"Server exited {child.returncode} after shutdown")
                    result["result"] = "pass"
                    result["diagnostics"] = diagnostics
                    result["goal"] = goal
                    if args.navigation:
                        result["definitions"] = definitions
                        result["restored_diagnostics"] = diagnostics_by_version[3]
                    break
    except BaseException as exc:
        result["result"] = "fail"
        result["error"] = f"{type(exc).__name__}: {exc}"
        raise
    finally:
        safe_stop(child)
        result["elapsed_s"] = round(time.monotonic() - start, 3)
        result["exit"] = child.poll() if child is not None else None
        if result["samples"]:
            result["peak_sampled_rss_mib"] = round(
                max(row["rss_kib"] for row in result["samples"]) / 1024, 1)
            result["min_memory_free_pct"] = min(
                row["memory_free_pct"] for row in result["samples"]
                if row["memory_free_pct"] is not None)
            result["min_disk_free_gib"] = round(
                min(row["disk_free_bytes"] for row in result["samples"]) / 1024**3, 2)
        result["trace_log"] = str(paths["events"])
        result["stdout_log"] = str(paths["stdout"])
        result["stderr_log"] = str(paths["stderr"])
        result["messages_log"] = str(paths["messages"])
        paths["result"].write_text(json.dumps(result, indent=2) + "\n")
        signal.signal(signal.SIGTERM, old_term)
        signal.signal(signal.SIGINT, old_int)
    print(json.dumps({key: result.get(key) for key in
                      ("label", "result", "exit", "abort", "elapsed_s",
                       "peak_sampled_rss_mib", "min_memory_free_pct",
                       "min_disk_free_gib", "goal_position")}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--env-file", type=Path, required=True)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--lean", type=Path)
    parser.add_argument("--immutable-root", type=Path, action="append", required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--goal-line", type=int,
                        help="0-based blank-line position; otherwise infer before trivial")
    parser.add_argument("--timeout-s", type=int, default=240)
    parser.add_argument("--navigation", action="store_true",
                        help="Check source definitions and unsaved False/True edits")
    parser.add_argument("--expected-aeneas-source", type=Path)
    parser.add_argument("--expected-mathlib-source", type=Path)
    args = parser.parse_args()
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9_.-]*", args.label):
        parser.error("--label must contain only letters, digits, dot, underscore, hyphen")
    run(args)


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(f"LSP probe failed: {type(exc).__name__}: {exc}", file=sys.stderr)
        sys.exit(1)
