# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Shared imports, the mock Lean server script, and environment helpers for
the `anneal-lsp` tests."""

from __future__ import annotations

import concurrent.futures
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import signal
import socket
import stat
import struct
import subprocess
import sys
import tempfile
import threading
import time
import types
from typing import Any
import unittest
from unittest import mock
import warnings

_CI_DIR = Path(__file__).resolve().parent.parent
if str(_CI_DIR) not in sys.path:
    sys.path.insert(0, str(_CI_DIR))

from anneal_lsp.cli import (  # noqa: E402
    _check_daemon_ping,
    default_socket_path,
    handle_mcp_request,
    main as cli_main,
    serve_mcp,
)
from anneal_lsp.client import (  # noqa: E402
    LspProcess,
    LspRpcError,
    _is_trusted_bwrap_path,
    build_sandbox_cmd,
    caller_homes,
    mask_lean_comments,
    py_col_to_utf16,
    uri_to_path,
    utf16_to_py_col,
)
from anneal_lsp.discovery import (  # noqa: E402
    PINNED_TOOLCHAIN,
    discover_workspace,
    find_lean_binary,
    find_lean_binary_optional,
)
from anneal_lsp.workspace import (  # noqa: E402
    WorkspacePool,
    WorkspaceWorker,
    _match_decl,
    _ro_tc,
)

_MOCK_LSP_SERVER = r"""
import json, os, sys, time

state = {"text": ""}

def read_msg():
    headers = {}
    while True:
        ln = sys.stdin.buffer.readline()
        if not ln:
            return None
        if ln in (b"\r\n", b"\n"):
            break
        k, v = ln.decode("ascii").split(":", 1)
        headers[k.strip().lower()] = v.strip()
    n = int(headers["content-length"])
    return json.loads(sys.stdin.buffer.read(n).decode("utf-8"))

def send(obj):
    raw = json.dumps(obj).encode("utf-8")
    sys.stdout.buffer.write(f"Content-Length: {len(raw)}\r\n\r\n".encode("ascii") + raw)
    sys.stdout.buffer.flush()

def mk_diag(sev, sl, sc, el, ec, msg):
    return {
        "severity": sev,
        "range": {"start": {"line": sl, "character": sc}, "end": {"line": el, "character": ec}},
        "message": msg,
    }

while True:
    msg = read_msg()
    if msg is None:
        break
    method, rid, params = msg.get("method"), msg.get("id"), msg.get("params") or {}
    if method == "initialize":
        send({"jsonrpc": "2.0", "id": rid, "result": {"capabilities": {}}})
    elif method in ("textDocument/didOpen", "textDocument/didChange"):
        doc = params["textDocument"]
        uri, ver = doc["uri"], doc["version"]
        text = (
            doc["text"]
            if method == "textDocument/didOpen"
            else params["contentChanges"][0]["text"]
        )
        state["text"] = text
        diags = []
        decl_ln = 0
        for idx, line in enumerate(text.splitlines()):
            s_ln = line.lstrip()
            if s_ln.startswith(("theorem ", "def ", "lemma ", "example ", "private ")):
                decl_ln = idx
            if "bad_tac" in line:
                diags.append(mk_diag(1, idx, 2, idx, 9, "unknown tactic `bad_tac`"))
            if "header_err" in line:
                diags.append(mk_diag(1, 0, 0, 0, 7, "header type mismatch"))
            if "prior_err" in line:
                diags.append(mk_diag(1, idx, 2, idx, 11, "prior tactic failed"))
            if "unsolved_step" in line:
                diags.append(
                    mk_diag(1, max(0, idx - 1), 0, idx, 15, "unsolved goals\ncase left\n⊢ 1 = 1")
                )
            if "sorry" in line or "hidden_admit_macro" in line:
                diags.append(mk_diag(2, decl_ln, 0, decl_ln, 7, "declaration uses `sorry`"))
        send({
            "jsonrpc": "2.0", "method": "$/lean/fileProgress",
            "params": {"textDocument": {"uri": uri, "version": ver}, "processing": []},
        })
        if "fatal_imp" in text:
            proc = [{"kind": 2, "range": {"start": {"line": 0, "character": 0}}}]
            send({
                "jsonrpc": "2.0", "method": "$/lean/fileProgress",
                "params": {"textDocument": {"uri": uri, "version": ver}, "processing": proc},
            })
            diags.append(mk_diag(1, 0, 0, 0, 1, "unknown module"))
        if "crash_wfd" in text or "drop_wfd" in text:
            proc = [{"kind": 2, "range": {"start": {"line": 0, "character": 0}}}]
            send({
                "jsonrpc": "2.0", "method": "$/lean/fileProgress",
                "params": {"textDocument": {"uri": uri, "version": ver}, "processing": proc},
            })
        if (
            "delay_diag" not in text
            and "exit_on_prog" not in text
            and "drop_wfd" not in text
        ):
            send({
                "jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                "params": {"uri": uri, "version": ver, "diagnostics": diags},
            })
    elif method == "textDocument/waitForDiagnostics":
        if "drop_wfd" in state["text"]:
            pass
        elif "crash_wfd" in state["text"]:
            send({"jsonrpc": "2.0", "id": rid,
                  "error": {"code": -32603, "message": "Lean file worker crashed"}})
        elif "unsupported_wfd" in state["text"] or "exit_on_prog" in state["text"]:
            send({"jsonrpc": "2.0", "id": rid,
                  "error": {"code": -32601, "message": "Method not found"}})
            if "exit_on_prog" in state["text"]:
                os._exit(0)
        else:
            if "delay_diag" in state["text"]:
                time.sleep(0.35)
                send({
                    "jsonrpc": "2.0", "method": "textDocument/publishDiagnostics",
                    "params": {
                        "uri": params["uri"], "version": params["version"],
                        "diagnostics": [mk_diag(1, 0, 0, 0, 5, "delayed diagnostic")],
                    },
                })
            send({"jsonrpc": "2.0", "id": rid, "result": {}})
    elif method == "$/lean/plainGoal":
        if "crash_wfd" in state["text"] or "drop_wfd" in state["text"]:
            time.sleep(2.0)
        ln0, ch0 = params["position"]["line"], params["position"]["character"]
        lines = state["text"].splitlines()
        cur = lines[ln0] if 0 <= ln0 < len(lines) else ""
        done = ("sorryAx", "«sorryAx»", "exact sorry", "header_err", "hidden_admit_macro")
        closed = any(k in cur for k in done) or ("rfl" in cur and ch0 >= cur.find("rfl") + 3)
        send({"jsonrpc": "2.0", "id": rid, "result": {"goals": [] if closed else ["⊢ 1 = 1"]}})
    elif method == "$/lean/plainTermGoal":
        send({"jsonrpc": "2.0", "id": rid, "result": {"goal": "⊢ 1 = 1"}})
    elif method == "textDocument/hover":
        if (
            "crash_wfd" in state["text"]
            or "drop_wfd" in state["text"]
            or "-- slow_hover" in state["text"]
        ):
            time.sleep(
                2.0 if ("crash_wfd" in state["text"] or "drop_wfd" in state["text"]) else 0.45
            )
        pos = params["position"]
        val = json.dumps({
            "lean_path": os.environ.get("LEAN_PATH", "NONE"),
            "home": os.environ.get("HOME", ""),
            "ld": os.environ.get("LD_LIBRARY_PATH", ""),
            "tmpdir": os.environ.get("TMPDIR", ""),
            "col": pos["character"],
        })
        send({"jsonrpc": "2.0", "id": rid,
              "result": {"contents": {"kind": "markdown", "value": val}}})
    elif method == "textDocument/definition":
        uri, pos = params["textDocument"]["uri"], params["position"]
        for ln_t in state["text"].splitlines():
            if ln_t.startswith("-- def_uri:"):
                uri = ln_t.split(":", 1)[1].strip()
                break
        rng = {"start": pos, "end": {"line": pos["line"], "character": pos["character"] + 1}}
        send({"jsonrpc": "2.0", "id": rid, "result": [{"uri": uri, "range": rng}]})
    elif method == "textDocument/completion":
        res = [{"label": "rfl", "detail": "Tactic", "kind": 6}]
        send({"jsonrpc": "2.0", "id": rid, "result": res})
    elif method == "textDocument/documentSymbol":
        rng = {"start": {"line": 0, "character": 0}}
        sym = {"name": "demo", "kind": 12, "detail": "1 = 1", "range": rng}
        send({"jsonrpc": "2.0", "id": rid, "result": [sym]})
    elif method == "shutdown":
        send({"jsonrpc": "2.0", "id": rid, "result": None})
    elif method == "exit":
        break
"""


def _scrubbed_env(extra: dict[str, str] | None = None) -> dict[str, str]:
    skip = ("CARGO_TARGET_DIR", "LEAN_PATH", "LEAN_SRC_PATH")
    clean = {k: v for k, v in os.environ.items() if not k.startswith("ANNEAL_") and k not in skip}
    if extra:
        clean.update(extra)
    return clean


def _maybe_live_lean() -> Path | None:
    try:
        if (lean_bin := find_lean_binary_optional()[0]) is not None:
            return lean_bin
    except FileNotFoundError:
        return None
    ci_lean = Path("/opt/anneal-nix/lean-toolchain/bin/lean")
    return ci_lean if ci_lean.is_file() else None


def _bwrap_usable(*, check_python: bool = False) -> bool:
    try:
        probe = [sys.executable, "-c", "pass"] if check_python else ["/bin/true"]
        cmd, is_sbx = build_sandbox_cmd(probe, sandbox=True)
    except (RuntimeError, PermissionError):
        return False
    if not is_sbx:
        return False
    return subprocess.run(cmd, capture_output=True, timeout=10).returncode == 0
