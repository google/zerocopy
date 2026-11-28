# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and live-Lean integration tests for `anneal/ci/anneal-lsp`."""

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

_CI_DIR = Path(__file__).resolve().parent
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


class DiscoveryAndProtocolTests(unittest.TestCase):
    def test_utf16_comment_masking_and_decl_match(self) -> None:
        astral = "def \U00010348 := 1"
        self.assertEqual(py_col_to_utf16(astral, 6), 7)
        self.assertEqual(utf16_to_py_col(astral, 7), 6)
        masked = mask_lean_comments(
            'def s := "\ntheorem fake : 1 = 2 := sorry\n" -- tail\n'
            'def r := r#"\ntheorem raw_fake := sorry\n"# /- nested /- -/ -/\n'
            'def z := r"trailing\\"\n'
            'def gap := "a\\\n  b"\n'
            "def keep_gap_line := sorry\n"
            'def hole := s!"prefix {(sorry : Nat)} suffix \\{sorry}"\n'
            "def char_hole := s!\"{(let _c := '}'; let _q := '\\''; "
            "let _u := '\\u007d'; let «}» := 1; (sorry : Nat))}\"\n"
            'def prime_hole := s!"{foo\' + bar\' + (sorry : Nat)}"\n'
            'def mg := «line1\n  sorry\n}»\n'
            'def mg_hole := s!"{(let «multi\n  sorry\n}» := 1; (sorry : Nat))}"\n'
            "def «sorry» : Nat := 1; def «admit» : Nat := 2\n"
            "theorem g_rs : False := «_root_».sorryAx _ false\n"
            'def neg_bool : Bool := !"{".isEmpty\n'
            "theorem after_neg : 1 = 1 := by\n"
            "  sorry\n"
            'def neg_lit : String := "sorry"\n'
            "theorem real : 1 = 1 := sorry\n"
        )
        m_lines = masked.splitlines()
        self.assertEqual(len(m_lines), 26)
        self.assertNotIn("sorry", "\n".join(m_lines[:9]))
        self.assertIn("sorry", m_lines[9])
        self.assertIn("sorry", m_lines[10])
        self.assertNotIn("\\{sorry}", m_lines[10])
        self.assertIn("sorry", m_lines[11])
        self.assertIn("sorry", m_lines[12])
        self.assertNotIn("sorry", "\n".join(m_lines[13:18]))
        self.assertIn("sorry", m_lines[18])
        t_redos = time.monotonic()
        self.assertIsNone(_match_decl("open " * 5000 + " " * 20000 + "x"))
        self.assertIsNone(_match_decl("open " + " " * 40000 + "x"))
        masked_open = mask_lean_comments(
            "open Foo -- " + "x" * 40000 + "\ntheorem ok : True := rfl"
        )
        ml_open = masked_open.splitlines()
        self.assertIsNone(_match_decl(ml_open[0]))
        self.assertEqual(_match_decl(ml_open[1]).group(2), "ok")
        self.assertLess(time.monotonic() - t_redos, 0.1)
        m_open_in = _match_decl("open Nat in theorem ok_in : 1 = 1 := rfl")
        self.assertIsNotNone(m_open_in)
        self.assertEqual(m_open_in.group(2), "ok_in")
        self.assertNotIn("sorry", m_lines[19])
        self.assertNotIn("admit", m_lines[19])
        self.assertIn("«_root_».sorryAx", m_lines[20])
        self.assertIn("sorry", m_lines[23])
        self.assertNotIn("sorry", m_lines[24])
        self.assertIn("sorry", m_lines[25])
        self.assertNotIn("nested", masked)
        with mock.patch("anneal_lsp.client.os.name", "nt"):
            self.assertEqual(uri_to_path("file:///C:/work/Mod.lean"), r"C:\work\Mod.lean")
            self.assertEqual(
                uri_to_path("file:///C%3A/work/Mod%201.lean"), r"C:\work\Mod 1.lean"
            )
            self.assertEqual(
                uri_to_path("file://localhost/C:/work/Mod.lean"), r"C:\work\Mod.lean"
            )
            self.assertEqual(
                uri_to_path("file://server/share/Mod.lean"), r"\\server\share\Mod.lean"
            )
        for decl in (
            "  @[simp] private theorem foo : 1 = 1 := by",
            "set_option maxRecDepth 100 in theorem bar : True := by",
            "opaque opqVal : Nat := 1",
        ):
            self.assertIsNotNone(_match_decl(decl), decl)

    def test_discovery_prebuilt_toolchain_and_lake_isolation(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            unit = root / "crate/proofs/unit_a"
            unit.mkdir(parents=True)
            (unit / "request.json").write_text("{}", encoding="utf-8")
            pf = unit / "Proof.lean"
            pf.write_text("theorem demo : 1 = 1 := sorry\n", encoding="utf-8")

            inst = root / "install"
            (inst / "lean/bin").mkdir(parents=True)
            (inst / "lean/lib/lean").mkdir(parents=True)
            fake_lean = inst / "lean/bin/lean"
            fake_lean.write_text("#!/bin/sh\n", encoding="utf-8")
            fake_lean.chmod(0o755)
            pb = inst / "share/anneal/prebuilt"
            (pb / "lib").mkdir(parents=True)
            (pb / "Trusted.olean").write_bytes(b"")

            # Prebuilt Trusted.olean alone must NOT silence unit artifact hint.
            env_no_art = _scrubbed_env({"ANNEAL_TEST_INSTALL_ROOT": str(inst)})
            with mock.patch.dict(os.environ, env_no_art, clear=True):
                ctx_miss = discover_workspace(pf)
            self.assertIn("--export-lean-lib", ctx_miss.missing_artifacts_hint() or "")

            art = root / "custom_art"
            (art / "lean-lib").mkdir(parents=True)
            (art / "lean-lib/Expected.olean").write_bytes(b"")
            (art / "capture").mkdir()
            env_art = _scrubbed_env({
                "ANNEAL_TEST_INSTALL_ROOT": str(inst), "ANNEAL_LSP_ARTIFACTS": str(art),
            })
            with mock.patch.dict(os.environ, env_art, clear=True):
                ctx = discover_workspace(pf)
            self.assertEqual(ctx.mode, "anneal_unit")
            self.assertIn(art.resolve() / "lean-lib", ctx.lean_path)
            self.assertIn(pb.resolve() / "lib", ctx.lean_path)
            self.assertIsNone(ctx.missing_artifacts_hint())

            # Theory dir accepts prebuilt Trusted.olean and warns if absent.
            repo = root / "zc"
            (repo / "anneal/trusted/lean").mkdir(parents=True)
            (repo / "anneal/trusted/lean/Trusted.lean").write_text("", encoding="utf-8")
            th = repo / "anneal/theory"
            th.mkdir()
            (th / "Mod.lean").write_text("def k := 1\n", encoding="utf-8")
            lean_env = _scrubbed_env({"ANNEAL_LEAN": str(fake_lean)})
            with mock.patch.dict(os.environ, lean_env, clear=True):
                self.assertIsNone(discover_workspace(th / "Mod.lean").missing_artifacts_hint())
            (pb / "Trusted.olean").unlink()
            for sub_p in ("trusted/lean/Trusted", "trusted/audit"):
                sd = repo / "anneal" / sub_p
                sd.mkdir(parents=True, exist_ok=True)
                (sd / "Sub.lean").write_text("def sub := 1\n", encoding="utf-8")
            with mock.patch.dict(os.environ, lean_env, clear=True):
                ctx_th = discover_workspace(th / "Mod.lean")
                ctx_tr = discover_workspace(repo / "anneal/trusted/lean/Trusted/Sub.lean")
                ctx_au = discover_workspace(repo / "anneal/trusted/audit/Sub.lean")
            self.assertEqual(ctx_th.mode, "lean_dir")
            self.assertTrue(ctx_tr.needs_anneal_prebuilt and ctx_au.needs_anneal_prebuilt)
            self.assertIn("prebuild_bundled_oleans.py", ctx_th.missing_artifacts_hint() or "")
            self.assertIn("<dir>/lib", ctx_th.missing_artifacts_hint() or "")

            # Sticky/world-writable ancestors never supply workspace roots.
            sticky = root / "sticky_tmp"
            sticky.mkdir()
            (sticky / "request.json").write_text("{}", encoding="utf-8")
            (sticky / "lakefile.lean").write_text("def x := 1\n", encoding="utf-8")
            (sticky / "Fake.olean").write_bytes(b"")
            (sticky / "scratch").mkdir()
            (sticky / "scratch/X.lean").write_text("def s := 1\n", encoding="utf-8")
            (sticky / "Direct.lean").write_text("def d := 1\n", encoding="utf-8")
            sticky.chmod(0o1777)
            try:
                with mock.patch.dict(os.environ, lean_env, clear=True):
                    ctx_sc = discover_workspace(sticky / "scratch/X.lean", home=root)
                    ctx_dir = discover_workspace(sticky / "Direct.lean", home=root)
                self.assertEqual(ctx_sc.mode, "lean_dir")
                self.assertEqual(ctx_sc.root, (sticky / "scratch").resolve())
                self.assertNotIn(sticky.resolve(), ctx_sc.lean_path)
                self.assertEqual(ctx_dir.mode, "lean_dir")
                self.assertNotIn(sticky.resolve(), ctx_dir.lean_path)
            finally:
                sticky.chmod(0o755)

            # Fallback locked SHA-256 digests stay synced with foundation-lock.
            from anneal_lsp.discovery import _DEFAULT_LOCKED_LEAN_SHA256  # noqa: E402
            lock_json = _CI_DIR.parent / "trusted/lean/foundation-lock.json"
            if lock_json.is_file():
                fl_dists = json.loads(lock_json.read_text("utf-8"))["distributions"]
                self.assertEqual(set(_DEFAULT_LOCKED_LEAN_SHA256), set(fl_dists.values()))

            # request.json beats lakefile.toml; ambient lake stays isolated.
            both = root / "both"
            both.mkdir()
            (both / "request.json").write_text("{}", encoding="utf-8")
            (both / "lakefile.toml").write_text('name = "demo"\n', encoding="utf-8")
            (both / "P.lean").write_text("def a := 1\n", encoding="utf-8")
            with mock.patch.dict(os.environ, lean_env, clear=True):
                self.assertEqual(discover_workspace(both / "P.lean").mode, "anneal_unit")

            other = root / "other/bin"
            other.mkdir(parents=True)
            (other / "lake").write_text("#!/bin/sh\n", encoding="utf-8")
            (other / "lake").chmod(0o755)
            home = root / "home"
            np_tc = home / ".elan/toolchains/leanprover--lean4---v4.99.0/bin"
            np_tc.mkdir(parents=True)
            (np_tc / "lean").write_text("#!/bin/sh\n", encoding="utf-8")
            (np_tc / "lean").chmod(0o755)
            proj = root / "proj"
            proj.mkdir()
            (proj / "lean-toolchain").write_text("leanprover/lean4:v4.99.0\n", encoding="utf-8")
            lean_path_env = {"ANNEAL_LEAN": str(fake_lean), "PATH": str(other)}
            with mock.patch.dict(os.environ, lean_path_env, clear=True):
                self.assertIsNone(find_lean_binary_optional(proj, home=home)[1])
            with mock.patch.dict(os.environ, {"PATH": str(other)}, clear=True):
                got = find_lean_binary_optional(proj, home=home)
                self.assertEqual(got, ((np_tc / "lean").resolve(), None))

            for bad_tc in ("..", "bad name", "   \n"):
                (proj / "lean-toolchain").write_text(bad_tc, encoding="utf-8")
                with mock.patch.dict(os.environ, {}, clear=True):
                    self.assertEqual(find_lean_binary_optional(proj, home=home), (None, None))
                    with self.assertRaises(FileNotFoundError):
                        find_lean_binary(proj, home=home)
            (proj / "lean-toolchain").write_bytes(b"\xff\xfe\x00")
            with mock.patch.dict(os.environ, {}, clear=True):
                self.assertEqual(find_lean_binary_optional(proj, home=home), (None, None))
            (home / ".cache/anneal/toolchain").mkdir(parents=True)
            with mock.patch.object(Path, "iterdir", side_effect=PermissionError("denied")):
                with mock.patch.dict(os.environ, {}, clear=True):
                    self.assertEqual(find_lean_binary_optional(both, home=home), (None, None))

            # Platform cache discovery (macOS Library/Caches & ~/anneal).
            mac_home = root / "mac_home"
            xdg_dir = root / "xdg_cache"
            mac_tc = mac_home / "Library/Caches/anneal/toolchain/v1/lean/bin"
            xdg_tc = xdg_dir / "anneal/toolchain/v1/lean/bin"
            home_tc = mac_home / "anneal/toolchain/v1/lean/bin"
            for tc_dir in (mac_tc, xdg_tc, home_tc):
                tc_dir.mkdir(parents=True)
                (tc_dir / "lean").write_text("#!/bin/sh\n", encoding="utf-8")
                (tc_dir / "lean").chmod(0o755)
            with mock.patch.dict(os.environ, {"XDG_CACHE_HOME": str(xdg_dir)}, clear=True):
                with mock.patch("anneal_lsp.discovery.sys.platform", "darwin"):
                    self.assertEqual(
                        find_lean_binary_optional(both, home=mac_home),
                        ((mac_tc / "lean").resolve(), None),
                    )
                with mock.patch("anneal_lsp.discovery.sys.platform", "linux"):
                    self.assertEqual(
                        find_lean_binary_optional(both, home=mac_home),
                        ((xdg_tc / "lean").resolve(), None),
                    )
            (mac_tc / "lean").unlink()
            with mock.patch("anneal_lsp.discovery.sys.platform", "darwin"):
                with mock.patch.dict(os.environ, {"XDG_CACHE_HOME": str(xdg_dir)}, clear=True):
                    self.assertEqual(
                        find_lean_binary_optional(both, home=mac_home),
                        ((home_tc / "lean").resolve(), None),
                    )
            # Locked toolchain SHA-256 wins over newer unpinned cache mtime.
            lock_home = root / "lock_home"
            old_tc = lock_home / ".cache/anneal/toolchain/v1_locked/lean/bin"
            new_tc = lock_home / ".cache/anneal/toolchain/v2_custom/lean/bin"
            old_tc.mkdir(parents=True)
            new_tc.mkdir(parents=True)
            (old_tc / "lean").write_bytes(b"pinned-lean-bin")
            (new_tc / "lean").write_bytes(b"custom-lean-bin")
            old_t = time.time() - 3600
            os.utime(old_tc / "lean", (old_t, old_t))
            pin_dig = frozenset({hashlib.sha256(b"pinned-lean-bin").hexdigest()})
            with mock.patch("anneal_lsp.discovery.sys.platform", "linux"):
                with mock.patch("anneal_lsp.discovery._LOCKED_LEAN_SHA256", pin_dig):
                    with mock.patch.dict(os.environ, {}, clear=True):
                        self.assertEqual(
                            find_lean_binary_optional(both, home=lock_home),
                            ((old_tc / "lean").resolve(), None),
                        )

            # Reject symlinked lean-toolchain files without reading targets.
            secret_tc = root / "secret_tc.txt"
            secret_tc.write_text("TOP_SECRET_PAYLOAD\n", encoding="utf-8")
            (proj / "lean-toolchain").unlink()
            (proj / "lean-toolchain").symlink_to(secret_tc)
            with mock.patch.dict(os.environ, {}, clear=True):
                self.assertEqual(find_lean_binary_optional(proj, home=home), (None, None))
                with self.assertRaises(FileNotFoundError) as exc_ctx:
                    find_lean_binary(proj, home=home)
            self.assertNotIn("TOP_SECRET_PAYLOAD", str(exc_ctx.exception))
            (proj / "lean-toolchain").unlink()
            (proj / "lean-toolchain").symlink_to(root / "missing_tc_target")
            with mock.patch.dict(os.environ, {}, clear=True):
                self.assertEqual(find_lean_binary_optional(proj, home=home), (None, None))

            # Nix symlinkJoin-style wrapper dir exposes sibling lake.
            nix_join = root / "nix_join/bin"
            nix_join.mkdir(parents=True)
            real_lake = root / "lake_store/bin/lake"
            real_lake.parent.mkdir(parents=True)
            real_lake.write_text("#!/bin/sh\n", encoding="utf-8")
            real_lake.chmod(0o755)
            (nix_join / "lean").symlink_to(fake_lean)
            (nix_join / "lake").symlink_to(real_lake)
            with mock.patch.dict(os.environ, {"ANNEAL_LEAN": str(nix_join / "lean")}, clear=True):
                got_l, got_lk = find_lean_binary_optional(proj, home=home)
            self.assertEqual((got_l, got_lk), (fake_lean.resolve(), real_lake.resolve()))

            # CLI forwards lake_bin for both symlinkJoin and omnibus+PATH-lake.
            lake_ws = root / "lake_cli_ws"
            lake_ws.mkdir()
            (lake_ws / "lakefile.toml").write_text('name = "cli_lk"\n', encoding="utf-8")
            (lake_ws / "Mod.lean").write_text("def lk := 1\n", encoding="utf-8")
            seen_lake_cmds: list[list[str]] = []

            class _LakeRec:
                def __init__(self, cmd: list[str], **_: Any) -> None:
                    seen_lake_cmds.append(cmd)
                    self.proc = mock.Mock(pid=4242)

                def request(self, *_: Any, **__: Any) -> dict[str, Any]:
                    return {}

                def notify(self, *_: Any, **__: Any) -> None:
                    pass

                def close(self) -> None:
                    pass

            omni_lean = root / "omni_lean/bin/lean"
            omni_lean.parent.mkdir(parents=True)
            omni_lean.write_text("#!/bin/sh\n", encoding="utf-8")
            omni_lean.chmod(0o755)
            path_lake_dir = root / "path_lake/bin"
            path_lake_dir.mkdir(parents=True)
            path_lake = path_lake_dir / "lake"
            path_lake.write_text("#!/bin/sh\n", encoding="utf-8")
            path_lake.chmod(0o755)
            with mock.patch("anneal_lsp.workspace.LspProcess", side_effect=_LakeRec), \
                 mock.patch("sys.stdout", new=io.StringIO()):
                with mock.patch.dict(
                    os.environ, _scrubbed_env({"ANNEAL_LEAN": str(nix_join / "lean")}),
                    clear=True,
                ):
                    self.assertEqual(
                        cli_main(["--direct", "--no-sandbox", "diag", str(lake_ws / "Mod.lean")]),
                        0,
                    )
                with mock.patch.dict(
                    os.environ,
                    _scrubbed_env({
                        "HOME": str(home),
                        "PATH": f"{omni_lean.parent}{os.pathsep}{path_lake_dir}",
                    }),
                    clear=True,
                ):
                    self.assertEqual(
                        cli_main(["--direct", "--no-sandbox", "diag", str(lake_ws / "Mod.lean")]),
                        0,
                    )
            self.assertEqual(seen_lake_cmds[0][0], str(real_lake.resolve()))
            self.assertEqual(seen_lake_cmds[1][0], str(path_lake.resolve()))

            # Ancestor scan for anneal/ stops at .git boundaries.
            par_git = root / "sibling_host"
            (par_git / "anneal/trusted/lean").mkdir(parents=True)
            (par_git / "anneal/trusted/lean/Trusted.lean").write_text("", encoding="utf-8")
            other_repo = par_git / "other_repo"
            (other_repo / ".git").mkdir(parents=True)
            (other_repo / "Main.lean").write_text("def x := 1\n", encoding="utf-8")
            with mock.patch.dict(os.environ, lean_env, clear=True):
                ctx_other = discover_workspace(other_repo / "Main.lean", home=home)
            self.assertFalse(any("anneal" in str(p) for p in ctx_other.lean_src_path))
            sym_host = root / "with_sym"
            sym_host.mkdir()
            (sym_host / "anneal").symlink_to(home)
            unrel = sym_host / "unrelated_repo"
            (unrel / ".git").mkdir(parents=True)
            (unrel / "Main.lean").write_text("def y := 1\n", encoding="utf-8")
            with mock.patch.dict(os.environ, lean_env, clear=True):
                ctx_unrel = discover_workspace(unrel / "Main.lean", home=home)
            self.assertEqual(ctx_unrel.root, unrel.resolve())

            # Explicit artifacts override ANNEAL_LSP_ARTIFACTS & uidless HOME.
            art_a, art_b = root / "art_a", root / "art_b"
            (art_a / "lean-lib").mkdir(parents=True)
            (art_b / "lean-lib").mkdir(parents=True)
            (art_a / "lean-lib/Expected.olean").write_bytes(b"")
            ov_unit = root / "ov_unit"
            ov_unit.mkdir()
            (ov_unit / "request.json").write_text("{}", encoding="utf-8")
            (ov_unit / "M.lean").write_text("def k := 1\n", encoding="utf-8")
            with mock.patch.dict(
                os.environ, {"ANNEAL_LSP_ARTIFACTS": str(root / "deleted_art")}, clear=True,
            ):
                ctx_del = discover_workspace(
                    ov_unit / "M.lean", artifacts_dir=art_b, explicit_lean=fake_lean,
                    use_env=True, home=home,
                )
                self.assertEqual(ctx_del.artifacts_dir, art_b.resolve())
            with mock.patch.dict(
                os.environ, {"ANNEAL_LSP_ARTIFACTS": str(art_a)}, clear=True,
            ):
                ctx_ov = discover_workspace(
                    ov_unit / "M.lean", artifacts_dir=art_b, explicit_lean=fake_lean,
                    use_env=True, home=home,
                )
            self.assertNotIn(art_a.resolve(), ctx_ov.lean_src_path)
            self.assertNotIn((art_a / "lean-lib").resolve(), ctx_ov.lean_path)
            self.assertIsNotNone(ctx_ov.missing_artifacts_hint())

            with mock.patch.dict(os.environ, {}, clear=True), \
                 mock.patch("pwd.getpwuid", side_effect=KeyError("no passwd")):
                self.assertEqual(caller_homes(), ())
                ctx_no_home = discover_workspace(
                    other_repo / "Main.lean", explicit_lean=fake_lean, use_env=True,
                )
                self.assertEqual(ctx_no_home.root, other_repo.resolve())
                _bwrap_usable()

            # Fail closed on symlinked `.olean`, workspace, and artifact paths.
            bad_olean_dir = root / "bad_oleans"
            bad_olean_dir.mkdir()
            (bad_olean_dir / "A_ok.olean").write_bytes(b"")
            (bad_olean_dir / "Z_bad.olean").symlink_to(fake_lean)
            sym_ol_u = root / "sym_ol_u"
            sym_ol_u.mkdir()
            (sym_ol_u / "request.json").write_text("{}", encoding="utf-8")
            (sym_ol_u / "M.lean").write_text("def z := 1\n", encoding="utf-8")
            with mock.patch.dict(os.environ, {}, clear=True):
                with self.assertRaises(PermissionError):
                    discover_workspace(sym_ol_u / "M.lean", artifacts_dir=bad_olean_dir, home=home)
            ssh_dir = home / ".ssh"
            ssh_dir.mkdir(parents=True)
            (ssh_dir / "Secret.olean").write_bytes(b"")
            sym_unit = root / "sym_unit"
            sym_unit.mkdir()
            (sym_unit / "request.json").write_text("{}", encoding="utf-8")
            (sym_unit / "Main.lean").write_text("def k := 1\n", encoding="utf-8")
            (sym_unit / "artifacts").mkdir()
            (sym_unit / "artifacts/lean-lib").symlink_to(ssh_dir)
            with mock.patch.dict(os.environ, {}, clear=True):
                with self.assertRaises(PermissionError):
                    discover_workspace(sym_unit / "Main.lean", home=home)
            (sym_unit / "artifacts/lean-lib").unlink()
            sym_parent = root / "sym_parent"
            sym_parent.symlink_to(home)
            with mock.patch.dict(os.environ, {}, clear=True):
                with self.assertRaises(PermissionError):
                    discover_workspace(
                        sym_unit / "Main.lean", artifacts_dir=sym_parent / ".ssh", home=home
                    )
            with mock.patch.dict(os.environ, {}, clear=True):
                with self.assertRaises(FileNotFoundError):
                    discover_workspace(
                        sym_unit / "Main.lean", artifacts_dir=root / "missing_art", home=home
                    )
                art_file = root / "not_a_dir.txt"
                art_file.write_text("x", encoding="utf-8")
                with self.assertRaises(NotADirectoryError):
                    discover_workspace(sym_unit / "Main.lean", artifacts_dir=art_file, home=home)
            with mock.patch.dict(
                os.environ, {"ANNEAL_LSP_ARTIFACTS": str(root / "missing_env_art")}, clear=True
            ):
                with self.assertRaises(FileNotFoundError):
                    discover_workspace(sym_unit / "Main.lean", home=home)
            (repo / "anneal/theory").rename(root / "real_theory")
            (repo / "anneal/theory").symlink_to(ssh_dir)
            with mock.patch.dict(os.environ, lean_env, clear=True):
                with self.assertRaises(PermissionError):
                    discover_workspace(repo / "anneal/trusted/lean/Trusted.lean", home=home)
            (repo / "anneal/theory").unlink()
            (root / "real_theory").rename(repo / "anneal/theory")

            # Reject symlinked target files and parent path components.
            priv = home / ".config/private"
            priv.mkdir(parents=True)
            secret_lean = priv / "Secret.lean"
            secret_lean.write_text("def topSecret := 99\n", encoding="utf-8")
            sym_file = sym_unit / "LinkProof.lean"
            sym_file.symlink_to(secret_lean)
            sym_sub = sym_unit / "sym_sub"
            sym_sub.symlink_to(priv)
            sym_cases = (sym_file, sym_sub / "Secret.lean", sym_sub / ".." / "Main.lean")
            with mock.patch.dict(os.environ, {}, clear=True):
                for bad_target in sym_cases:
                    with self.assertRaises(PermissionError):
                        discover_workspace(bad_target, home=home)
                    with mock.patch("sys.stderr", new=io.StringIO()):
                        self.assertEqual(
                            cli_main(["--direct", "--no-sandbox", "diag", str(bad_target)]), 1
                        )
                        self.assertEqual(cli_main(["diag", str(bad_target)]), 1)
                        self.assertEqual(cli_main(["discover", str(bad_target)]), 1)
                with mock.patch("sys.stderr", new=io.StringIO()):
                    self.assertEqual(cli_main(["--direct", "outline", str(sym_sub)]), 1)

            # Lake output .olean overwrites invalidate worker fingerprint.
            lk_w = root / "lake_watch"
            lk_ol_dir = lk_w / ".lake/build/lib/lean"
            lk_ol_dir.mkdir(parents=True)
            (lk_w / "lakefile.toml").write_text('name = "demo"\n', encoding="utf-8")
            (lk_w / "Demo.lean").write_text("def k := 1\n", encoding="utf-8")
            lk_ol = lk_ol_dir / "Demo.olean"
            lk_ol.write_bytes(b"v1")
            fp1 = discover_workspace(lk_w / "Demo.lean").fingerprint()
            ds, os_st = lk_ol_dir.stat(), lk_ol.stat()
            lk_ol.write_bytes(b"v2")
            os.utime(lk_ol, ns=(os_st.st_atime_ns, os_st.st_mtime_ns + 5_000_000))
            os.utime(lk_ol_dir, ns=(ds.st_atime_ns, ds.st_mtime_ns))
            fp2 = discover_workspace(lk_w / "Demo.lean").fingerprint()
            self.assertNotEqual(fp1, fp2)
            (lk_w / "lake-manifest.json").write_text('{"version": 7}\n', encoding="utf-8")
            fp3 = discover_workspace(lk_w / "Demo.lean").fingerprint()
            self.assertNotEqual(fp2, fp3)

    def test_sandbox_socket_and_hung_close_guards(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            ws = root / "ws"
            ws.mkdir()
            (ws / "Demo.lean").write_text("def x := 1\n", encoding="utf-8")

            res = subprocess.run(
                [sys.executable, "-B", str(_CI_DIR / "anneal-lsp"), "--direct", "--no-sandbox",
                 "diag", str(ws / "Demo.lean")],
                cwd=str(root), env={"PATH": "/usr/bin:/bin", "HOME": str(root / "nohome")},
                text=True, capture_output=True, timeout=15,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn(PINNED_TOOLCHAIN, res.stderr)

            # Hung child ignoring SIGTERM exits without deadlock.
            proc = LspProcess(
                ["/bin/sh", "-c", "trap '' TERM; while :; do sleep 1; done"],
                cwd=root, env={"PATH": os.environ.get("PATH", "/usr/bin:/bin")},
            )
            t0 = time.monotonic()
            proc.close()
            self.assertLess(time.monotonic() - t0, 5.0)
            self.assertIsNotNone(proc.proc.poll())

            if shutil.which("bwrap"):
                nested_home, nested_xdg = ws / "secret_home", ws / "xdg_rt"
                nested_home.mkdir()
                nested_xdg.mkdir()
                with mock.patch.dict(os.environ, {"XDG_RUNTIME_DIR": str(nested_xdg)}, clear=False):
                    cmd, is_sbx = build_sandbox_cmd(
                        ["/bin/true"], ro_binds=[ws], hidden_homes=[nested_home], sandbox=True
                    )
                self.assertTrue(is_sbx)
                self.assertEqual(cmd[1:3], ["--tmpfs", "/"])
                for idx in range(len(cmd) - 2):
                    self.assertNotEqual(cmd[idx : idx + 3], ["--ro-bind", "/", "/"])
                self.assertNotIn("/nix/var/nix/daemon-socket", cmd)
                for flag in (
                    "--unshare-ipc", "--unshare-pid", "--unshare-net", "--die-with-parent",
                    "--new-session",
                ):
                    self.assertIn(flag, cmd)
                self.assertIn("--cap-drop", cmd)
                self.assertEqual(cmd[cmd.index("--cap-drop") + 1], "ALL")
                ro_idx = max(i for i, t in enumerate(cmd)
                             if t == "--ro-bind" and cmd[i + 1] == str(ws.resolve()))
                for hidden in (nested_home, nested_xdg):
                    hs = str(hidden.resolve())
                    self.assertTrue(
                        any(cmd[i] == "--tmpfs" and cmd[i + 1] == hs
                            for i in range(ro_idx, len(cmd) - 1))
                    )
                real_h, scratch_h = root / "real_pw_home", root / "scratch_env_home"
                real_h.mkdir()
                (real_h / ".local/bin").mkdir(parents=True)
                scratch_h.mkdir()
                fake_pw_home = Path("/home/mock_pw_home")
                orig_exists, orig_res = Path.exists, Path.resolve
                orig_is_dir = Path.is_dir
                with mock.patch.dict(os.environ, {"HOME": str(scratch_h)}, clear=True), \
                     mock.patch("pwd.getpwuid", return_value=mock.Mock(pw_dir=str(real_h))), \
                     mock.patch("anneal_lsp.client._find_trusted_bwrap",
                                return_value="/usr/bin/bwrap"):
                    rh_cmd, rh_ok = build_sandbox_cmd(
                        ["/bin/true"], ro_binds=[root], work_dir=ws, sandbox=True,
                    )
                    self.assertTrue(rh_ok)
                    r_idx = rh_cmd.index(str(root.resolve()))
                    self.assertIn(str(real_h.resolve()), rh_cmd[r_idx:])
                with mock.patch.dict(os.environ, {"HOME": str(scratch_h)}, clear=True), \
                     mock.patch(
                         "pwd.getpwuid", return_value=mock.Mock(pw_dir=str(fake_pw_home))
                     ), \
                     mock.patch("anneal_lsp.client._find_trusted_bwrap",
                                return_value="/usr/bin/bwrap"), \
                     mock.patch.object(
                         Path, "exists",
                         lambda s: True if s == fake_pw_home else orig_exists(s),
                     ), \
                     mock.patch.object(
                         Path, "is_dir",
                         lambda s: True if s == fake_pw_home else orig_is_dir(s),
                     ), \
                     mock.patch.object(
                         Path, "resolve",
                         lambda s: fake_pw_home if s == fake_pw_home else orig_res(s),
                     ):
                    fpw_cmd, fpw_ok = build_sandbox_cmd(
                        ["/bin/true"], ro_binds=[ws], work_dir=ws, sandbox=True,
                    )
                    self.assertTrue(fpw_ok)
                    self.assertIn(str(fake_pw_home), fpw_cmd)
                with mock.patch.dict(os.environ, {}, clear=True), \
                     mock.patch("pwd.getpwuid", side_effect=KeyError("uidless")), \
                     mock.patch("anneal_lsp.client._find_trusted_bwrap",
                                return_value="/usr/bin/bwrap"):
                    _, uh_ok = build_sandbox_cmd(["/bin/true"], work_dir=ws, sandbox=True)
                    self.assertTrue(uh_ok)
                # Non-hidden host ro_binds outside hidden dirs stay mounted.
                fake_ext = Path("/opt/fake_nonhidden_ws")
                with mock.patch("anneal_lsp.client._find_trusted_bwrap",
                                return_value="/usr/bin/bwrap"), \
                     mock.patch("anneal_lsp.client.caller_homes", return_value=()), \
                     mock.patch("anneal_lsp.client._SYS_RO_DIRS", ()), \
                     mock.patch("anneal_lsp.client._ETC_RO_PATHS", ()), \
                     mock.patch("anneal_lsp.client._SYS_RO_LINKS", ()), \
                     mock.patch.object(
                         Path, "exists", lambda s: True if s == fake_ext else orig_exists(s)
                     ), \
                     mock.patch.object(
                         Path, "resolve", lambda s: fake_ext if s == fake_ext else orig_res(s)
                     ):
                    nh_cmd, _ = build_sandbox_cmd(
                        ["/bin/true"], ro_binds=[fake_ext], sandbox=True,
                    )
                    self.assertIn(str(fake_ext), nh_cmd)
                # Broad host roots (/home, /var, /tmp) stay off _ro_tc & rehide.
                mld = root / "my_lean_dir"
                mld.mkdir()
                (mld / "lean").write_text("#!/bin/sh\n", encoding="utf-8")
                self.assertEqual(_ro_tc(mld / "lean"), [mld.resolve(), mld.resolve()])
                mld_cmd, _ = build_sandbox_cmd(
                    ["/bin/true"], ro_binds=_ro_tc(mld / "lean"), sandbox=True,
                )
                self.assertIn(str(mld.resolve()), mld_cmd)
                with mock.patch("anneal_lsp.client._find_trusted_bwrap",
                                return_value="/usr/bin/bwrap"), \
                     mock.patch.object(Path, "exists", lambda _: True), \
                     mock.patch.object(Path, "is_dir", lambda _: False), \
                     mock.patch.object(Path, "resolve", lambda s: s):
                    self.assertNotIn(Path("/home"), _ro_tc(Path("/home/sbx/lean")))
                    self.assertIn(Path("/home/sbx"), _ro_tc(Path("/home/sbx/lean")))
                    self.assertNotIn(Path("/var"), _ro_tc(Path("/var/bin/lean")))
                    self.assertIn(Path("/var/bin"), _ro_tc(Path("/var/bin/lean")))
                    self.assertNotIn(Path("/usr"), _ro_tc(Path("/usr/bin/lean")))
                    self.assertIn(Path("/usr/bin"), _ro_tc(Path("/usr/bin/lean")))
                    self.assertNotIn(Path("/usr/local"), _ro_tc(Path("/usr/local/bin/lean")))
                    self.assertIn(Path("/usr/local/bin"), _ro_tc(Path("/usr/local/bin/lean")))
                    self.assertNotIn(Path("/tmp"), _ro_tc(Path("/tmp/bare_lean")))
                    self.assertIn(Path("/tmp/bare_lean"), _ro_tc(Path("/tmp/bare_lean")))
                proj_bin = root / "Projects/bin/lean"
                proj_bin.parent.mkdir(parents=True)
                proj_bin.write_text("#!/bin/sh\n", encoding="utf-8")
                self.assertEqual(_ro_tc(proj_bin), [proj_bin.parent.resolve()] * 2)
                tc_ok = root / "tc_ok"
                (tc_ok / "bin").mkdir(parents=True)
                (tc_ok / "lib/lean").mkdir(parents=True)
                (tc_ok / "bin/lean").write_text("#!/bin/sh\n", encoding="utf-8")
                self.assertEqual(_ro_tc(tc_ok / "bin/lean"), [tc_ok.resolve()] * 2)
                eh_u = root / "elan_home_unit"
                ed_u = eh_u / ".elan"
                (ed_u / "bin").mkdir(parents=True)
                (ed_u / "toolchains/t1/lib/lean").mkdir(parents=True)
                (ed_u / "settings.toml").write_text("default_toolchain = 't1'\n", encoding="utf-8")
                (ed_u / "bin/elan").write_text("#!/bin/sh\n", encoding="utf-8")
                os.link(ed_u / "bin/elan", ed_u / "bin/lean")
                with mock.patch.dict(os.environ, {"HOME": str(eh_u)}, clear=False):
                    tc_elan = {p.resolve() for p in _ro_tc(ed_u / "bin/lean")}
                self.assertIn((ed_u / "bin").resolve(), tc_elan)
                self.assertIn((ed_u / "toolchains").resolve(), tc_elan)
                self.assertIn((ed_u / "settings.toml").resolve(), tc_elan)
                self.assertNotIn(eh_u.resolve(), tc_elan)
                with mock.patch("anneal_lsp.client._find_trusted_bwrap",
                                return_value="/usr/bin/bwrap"):
                    var_cmd, _ = build_sandbox_cmd(
                        ["/bin/true"], ro_binds=[Path("/var")], sandbox=True,
                    )
                    var_i = max(i for i, t in enumerate(var_cmd)
                                if t == "--ro-bind" and var_cmd[i + 1] == "/var")
                    self.assertTrue(
                        any(var_cmd[i] == "--tmpfs" and var_cmd[i + 1] == "/var/tmp"
                            for i in range(var_i, len(var_cmd) - 1))
                    )
                    # Ancestor bind before rehide keeps nested ws visible.
                    anc_p = root / "anc_prefix"
                    anc_h = anc_p / "home/alice"
                    anc_ws = anc_h / "ws"
                    anc_ws.mkdir(parents=True)
                    anc_cmd, _ = build_sandbox_cmd(
                        ["/bin/true"], ro_binds=[anc_p, anc_ws],
                        hidden_homes=[anc_h], work_dir=anc_ws, sandbox=True,
                    )
                    h_i = anc_cmd.index(str(anc_h.resolve()))
                    ws_i = max(i for i, t in enumerate(anc_cmd)
                               if t == "--ro-bind" and anc_cmd[i + 1] == str(anc_ws.resolve()))
                    self.assertLess(h_i, ws_i)
            else:
                with mock.patch("anneal_lsp.client.sys.platform", "linux"):
                    with self.assertRaisesRegex(RuntimeError, "bwrap"):
                        build_sandbox_cmd(["/bin/true"], sandbox=True)

            # Reject hidden workspace roots, `.lake` hardlinks, & loader env.
            self.assertFalse(_is_trusted_bwrap_path("/nonexistent/bwrap"))
            with mock.patch.object(Path, "exists", return_value=False):
                self.assertFalse(_is_trusted_bwrap_path("/usr/bin/bwrap"))
            with mock.patch("anneal_lsp.client.shutil.which", return_value="/usr/bin/bwrap"), \
                 mock.patch("anneal_lsp.client._is_trusted_bwrap_path", return_value=True):
                with self.assertRaisesRegex(PermissionError, "hidden workspace root"):
                    build_sandbox_cmd(["/bin/true"], work_dir=Path("/tmp"), sandbox=True)
                cap_cmd, cap_sbx = build_sandbox_cmd(["/bin/true"], work_dir=ws, sandbox=True)
                self.assertTrue(cap_sbx)
                self.assertEqual(cap_cmd[cap_cmd.index("--cap-drop") + 1], "ALL")
                self.assertIn("--new-session", cap_cmd)
                hl_ws = root / "hl_lake_ws"
                (hl_ws / ".lake/build").mkdir(parents=True)
                (hl_ws / "lakefile.toml").write_text('name = "hl"\n', encoding="utf-8")
                (hl_ws / "Demo.lean").write_text("def x := 1\n", encoding="utf-8")
                clean_bin = hl_ws / ".lake/build/clean.bin"
                clean_bin.write_text("ok\n", encoding="utf-8")
                ok_cmd, ok_sbx = build_sandbox_cmd(
                    ["/bin/true"], writable_dirs=[hl_ws / ".lake"], sandbox=True
                )
                self.assertTrue(ok_sbx and "--bind" in ok_cmd)
                host_target = root / "host_secret_inode.txt"
                host_target.write_text("HOST_SECRET\n", encoding="utf-8")
                os.link(host_target, hl_ws / ".lake/build/hard.bin")
                with self.assertRaisesRegex(PermissionError, "hardlinked"):
                    build_sandbox_cmd(
                        ["/bin/true"], writable_dirs=[hl_ws / ".lake"], sandbox=True
                    )
                hl_tc = root / "hl_tc"
                hl_tc.mkdir()
                for bn in ("lean", "lake"):
                    (hl_tc / bn).write_text("#!/bin/sh\n", encoding="utf-8")
                    (hl_tc / bn).chmod(0o755)
                hl_ctx = discover_workspace(hl_ws / "Demo.lean", explicit_lean=hl_tc / "lean")
                with self.assertRaisesRegex(PermissionError, "hardlinked"):
                    WorkspaceWorker(hl_ctx, sandbox=True)

            # Reject untrusted PATH `bwrap` & hide/reject custom socket dirs.
            # Allow Nix `/nix/store` sticky 01775; keep store children strict.
            nix_bwrap = "/nix/store/000000-bwrap/bin/bwrap"
            orig_exists, orig_res = Path.exists, Path.resolve
            orig_lstat, orig_is_file = Path.lstat, Path.is_file

            def _mk_st(mode: int, uid: int = 0) -> os.stat_result:
                return os.stat_result((mode, 1, 1, 1, uid, 0, 0, 0, 0, 0))

            for nix_mode, child_mode, expected in (
                (stat.S_IFDIR | 0o1775, stat.S_IFDIR | 0o0555, True),
                (stat.S_IFDIR | 0o0775, stat.S_IFDIR | 0o0555, False),
                (stat.S_IFDIR | 0o1777, stat.S_IFDIR | 0o0555, False),
                (stat.S_IFDIR | 0o1775, stat.S_IFDIR | 0o1775, False),
            ):
                modes = {
                    "/": stat.S_IFDIR | 0o0755,
                    "/nix": stat.S_IFDIR | 0o0755,
                    "/nix/store": nix_mode,
                    "/nix/store/000000-bwrap": child_mode,
                    "/nix/store/000000-bwrap/bin": stat.S_IFDIR | 0o0555,
                    nix_bwrap: stat.S_IFREG | 0o0555,
                }
                with mock.patch.object(
                    Path, "exists", lambda s, _m=modes: True if str(s) in _m else orig_exists(s)
                ), mock.patch.object(
                    Path, "resolve", lambda s, _m=modes: s if str(s) in _m else orig_res(s)
                ), mock.patch.object(
                    Path, "is_file", lambda s, _m=modes: True if str(s) == nix_bwrap
                    else orig_is_file(s)
                ), mock.patch.object(
                    Path, "lstat", lambda s, _m=modes: _mk_st(_m[str(s)]) if str(s) in _m
                    else orig_lstat(s)
                ):
                    self.assertEqual(_is_trusted_bwrap_path(nix_bwrap), expected,
                                     (oct(nix_mode), oct(child_mode)))
            evil_bin = root / "evil_bin"
            evil_bin.mkdir()
            (evil_bin / "bwrap").write_text("#!/bin/sh\nexit 1\n", encoding="utf-8")
            (evil_bin / "bwrap").chmod(0o755)
            with mock.patch.dict(os.environ, {"PATH": str(evil_bin)}, clear=False), \
                 mock.patch("anneal_lsp.client._SYS_BWRAP_PATH", ""):
                with self.assertRaisesRegex(PermissionError, "untrusted"):
                    build_sandbox_cmd(["/bin/true"], work_dir=ws, sandbox=True)
            with mock.patch("anneal_lsp.client.shutil.which", return_value="/usr/bin/bwrap"), \
                 mock.patch("anneal_lsp.client._is_trusted_bwrap_path", return_value=True):
                ws_sock_dir = ws / ".anneal"
                ws_sock_dir.mkdir(mode=0o700)
                cmd_s, is_s = build_sandbox_cmd(
                    ["/bin/true"], ro_binds=[ws], hidden_paths=[ws_sock_dir],
                    work_dir=ws, sandbox=True,
                )
                self.assertTrue(is_s)
                ro_ws_i = cmd_s.index(str(ws.resolve()))
                self.assertTrue(any(
                    cmd_s[i] == "--tmpfs" and cmd_s[i + 1] == str(ws_sock_dir.resolve())
                    for i in range(ro_ws_i, len(cmd_s) - 1)
                ))
                with self.assertRaisesRegex(PermissionError, "overlaps"):
                    build_sandbox_cmd(
                        ["/bin/true"], ro_binds=[ws], hidden_paths=[ws],
                        work_dir=ws, sandbox=True,
                    )
            fake_bin = root / "ld_lean/lean"
            fake_bin.parent.mkdir(parents=True)
            fake_bin.write_text("#!/bin/sh\n", encoding="utf-8")
            fake_bin.chmod(0o755)
            ctx_ld = discover_workspace(ws / "Demo.lean", explicit_lean=fake_bin)
            seen_spawns: list[tuple[list[str], Path, dict[str, str]]] = []

            class _RecProc:
                def __init__(self, cmd: list[str], *, cwd: Path, env: dict[str, str], **_: Any):
                    seen_spawns.append((cmd, cwd, env))
                    self.proc = mock.Mock(pid=9999)

                def request(self, *_: Any, **__: Any) -> dict[str, Any]:
                    return {}

                def notify(self, *_: Any, **__: Any) -> None:
                    pass

                def close(self) -> None:
                    pass

            with mock.patch.dict(
                os.environ,
                {
                    "LD_LIBRARY_PATH": ".:rel/lib:/opt/lean/lib",
                    "TMPDIR": "/tmp/host_tmp", "TEMP": "/tmp/host_tmp", "TMP": "/tmp/host_tmp",
                },
                clear=False,
            ):
                with mock.patch("anneal_lsp.client.shutil.which", return_value="/usr/bin/bwrap"), \
                     mock.patch("anneal_lsp.client._is_trusted_bwrap_path", return_value=True), \
                     mock.patch("anneal_lsp.workspace.LspProcess", side_effect=_RecProc):
                    WorkspaceWorker(ctx_ld, sandbox=True).close()
                    WorkspaceWorker(ctx_ld, sandbox=False).close()
            with mock.patch.dict(os.environ, {}, clear=True), \
                 mock.patch("pwd.getpwuid", side_effect=KeyError("uidless")), \
                 mock.patch("anneal_lsp.workspace.LspProcess", side_effect=_RecProc):
                WorkspaceWorker(ctx_ld, sandbox=False).close()
            self.assertEqual(seen_spawns[2][2]["PATH"], str(fake_bin.parent))
            sbx_cmd, sbx_cwd, sbx_env = seen_spawns[0]
            self.assertEqual(sbx_cwd, Path("/"))
            self.assertNotIn("LD_LIBRARY_PATH", sbx_env)
            for tk in ("TMPDIR", "TEMP", "TMP"):
                self.assertNotIn(tk, sbx_env)
                self.assertEqual(seen_spawns[1][2].get(tk), "/tmp/host_tmp")
            self.assertIn("--chdir", sbx_cmd)
            self.assertIn("--unsetenv", sbx_cmd)
            self.assertIn("--setenv", sbx_cmd)
            si = sbx_cmd.index("--setenv")
            self.assertEqual(sbx_cmd[si + 1 : si + 3], ["LD_LIBRARY_PATH", "/opt/lean/lib"])
            self.assertEqual(seen_spawns[1][1], ctx_ld.root)
            self.assertEqual(seen_spawns[1][2].get("LD_LIBRARY_PATH"), "/opt/lean/lib")

            # LspProcess.close cleans pipes & waits even after child EOF.
            with warnings.catch_warnings(record=True) as rw:
                warnings.simplefilter("always", ResourceWarning)
                exited_p = LspProcess(
                    ["/bin/sh", "-c", "exit 1"],
                    cwd=root, env={"PATH": os.environ.get("PATH", "/usr/bin:/bin")},
                )
                in_fh, out_fh = exited_p.proc.stdin, exited_p.proc.stdout
                assert in_fh is not None and out_fh is not None
                dl_eof = time.monotonic() + 5.0
                while not exited_p._closed and time.monotonic() < dl_eof:
                    time.sleep(0.02)
                exited_p.close()
                self.assertTrue(in_fh.closed and out_fh.closed)
                self.assertEqual(exited_p.proc.poll(), 1)
            self.assertEqual([w for w in rw if issubclass(w.category, ResourceWarning)], [])

            # Daemon spawn drops loader/Python env, uses -I & cwd=/, & try tmo.
            from anneal_lsp import cli as lsp_cli  # noqa: E402

            d_spawns: list[tuple[list[str], str, dict[str, str]]] = []

            class _FakeDProc:
                def poll(self) -> None:
                    return None

            def fake_popen(cmd: list[str], *, cwd: str, env: dict[str, str], **_: Any) -> Any:
                d_spawns.append((cmd, cwd, env))
                return _FakeDProc()

            ok_ping = {
                "version": lsp_cli.SERVER_VERSION,
                "build_id": lsp_cli.SERVER_BUILD_ID,
                "sandbox": True,
            }
            bad_ping = {**ok_ping, "sandbox": False}
            d_sock = root / "d_guard/lsp.sock"
            with mock.patch.dict(
                os.environ,
                {
                    "LD_LIBRARY_PATH": ".:/opt/lib", "LD_PRELOAD": "evil.so",
                    "PYTHONPATH": str(root / "poison_py"), "PYTHONSTARTUP": str(root / "p.py"),
                },
                clear=False,
            ):
                with mock.patch(
                    "anneal_lsp.cli._check_daemon_ping", side_effect=[None, None, ok_ping]
                ), mock.patch("anneal_lsp.cli.subprocess.Popen", side_effect=fake_popen):
                    lsp_cli._ensure_daemon(str(d_sock), sandbox=True)
                with mock.patch(
                    "anneal_lsp.cli._check_daemon_ping", side_effect=[None, None, bad_ping]
                ), mock.patch("anneal_lsp.cli.subprocess.Popen", side_effect=fake_popen):
                    with self.assertRaisesRegex(RuntimeError, "sandbox disabled"):
                        lsp_cli._ensure_daemon(str(root / "d_bad/lsp.sock"), sandbox=True)
            self.assertIn("-I", d_spawns[0][0])
            self.assertEqual(d_spawns[0][1], "/")
            for bad_env in ("LD_LIBRARY_PATH", "LD_PRELOAD", "PYTHONPATH", "PYTHONSTARTUP"):
                self.assertNotIn(bad_env, d_spawns[0][2])

            # stop_daemon waits for concurrent launcher lock before returning.
            import fcntl as _fcntl  # noqa: E402

            race_dir = root / "stop_race"
            race_dir.mkdir(mode=0o700)
            race_sock = race_dir / "lsp.sock"
            lfd = os.open(f"{race_sock}.lock", os.O_CREAT | os.O_RDWR, 0o600)
            _fcntl.flock(lfd, _fcntl.LOCK_EX)
            events: list[str] = []

            def rel_lock() -> None:
                time.sleep(0.15)
                events.append("launched")
                _fcntl.flock(lfd, _fcntl.LOCK_UN)
                os.close(lfd)

            r_th = threading.Thread(target=rel_lock, daemon=True)
            r_th.start()
            with mock.patch(
                "anneal_lsp.cli._unix_call",
                side_effect=lambda *a, **kw: (events.append("shutdown"), {"ok": True})[1],
            ):
                lsp_cli.stop_daemon(str(race_sock), timeout_s=2.0)
            r_th.join(timeout=2.0)
            self.assertEqual(events, ["launched", "shutdown"])
            to_dir = root / "stop_to"
            to_dir.mkdir(mode=0o700)
            to_sock = to_dir / "lsp.sock"
            sfd = os.open(f"{to_sock}.srv.lock", os.O_CREAT | os.O_RDWR, 0o600)
            _fcntl.flock(sfd, _fcntl.LOCK_EX)
            try:
                with self.assertRaises(TimeoutError):
                    lsp_cli.stop_daemon(str(to_sock), timeout_s=0.1)
                with mock.patch.dict(
                    os.environ, {"ANNEAL_LSP_SOCKET": str(to_sock)}, clear=False
                ), mock.patch("anneal_lsp.cli.stop_daemon", side_effect=TimeoutError("tmo")), \
                     mock.patch("sys.stderr", new=io.StringIO()):
                    self.assertEqual(cli_main(["stop-daemon"]), 1)
            finally:
                _fcntl.flock(sfd, _fcntl.LOCK_UN)
                os.close(sfd)
            custom_s = root / "explicit_stop/lsp.sock"
            with mock.patch("anneal_lsp.cli.stop_daemon", return_value=0) as mk_sd:
                self.assertEqual(cli_main(["stop-daemon", "--socket", str(custom_s)]), 0)
            mk_sd.assert_called_once_with(str(custom_s))

            # Startup timeout kills and reaps hung daemon process.
            hung_procs: list[subprocess.Popen[Any]] = []
            real_popen = subprocess.Popen

            def fake_hung_popen(*_: Any, **__: Any) -> subprocess.Popen[Any]:
                p = real_popen(["/bin/sh", "-c", "sleep 30"], start_new_session=True)
                hung_procs.append(p)
                return p

            ticks = iter([0.0, 0.0, 11.0, 11.0])
            hung_sock = root / "hung_start/lsp.sock"
            with mock.patch("anneal_lsp.cli._check_daemon_ping", return_value=None), \
                 mock.patch("anneal_lsp.cli.subprocess.Popen", side_effect=fake_hung_popen), \
                 mock.patch("anneal_lsp.cli.time.monotonic", side_effect=lambda: next(ticks, 12.0)):
                with self.assertRaisesRegex(RuntimeError, "Failed to start"):
                    lsp_cli._ensure_daemon(str(hung_sock), sandbox=True)
            self.assertIsNotNone(hung_procs[0].poll())
            seen_tm: list[float] = []

            def fake_uc(sock: str, act: str, a: dict[str, Any], timeout_s: float = 0.0) -> Any:
                seen_tm.append(timeout_s)
                return {"ok": True, "result": {"text": "ok"}}

            with mock.patch("anneal_lsp.cli._ensure_daemon"), \
                 mock.patch("anneal_lsp.cli.default_socket_path",
                            return_value=str(root / "tm_sock/lsp.sock")), \
                 mock.patch("anneal_lsp.cli._abs_args", return_value={}), \
                 mock.patch("anneal_lsp.cli._unix_call", side_effect=fake_uc), \
                 mock.patch("sys.stdout", new=io.StringIO()):
                self.assertEqual(cli_main(["try", str(ws / "Demo.lean"), "1", "rfl"]), 0)
                self.assertEqual(cli_main(["diag", str(ws / "Demo.lean")]), 0)
            self.assertGreater(seen_tm[0], 400.0)
            self.assertEqual(seen_tm[1], 270.0)

            sym_sock = root / "sym.sock"
            sym_sock.symlink_to(root / "elsewhere.sock")
            with mock.patch.dict(os.environ, {"ANNEAL_LSP_SOCKET": str(sym_sock)}, clear=False):
                with mock.patch("sys.stderr", new=io.StringIO()):
                    self.assertEqual(cli_main(["diag", str(ws / "Demo.lean")]), 1)

            # Non-POSIX (Windows-like) hosts import CLI/MCP without `fcntl`.
            win_probe = "\n".join([
                "import io, json, socketserver, sys",
                "from pathlib import Path",
                "from unittest import mock",
                f"sys.path.insert(0, {str(_CI_DIR)!r})",
                "sys.modules['fcntl'] = None",
                "with mock.patch.object(socketserver, 'UnixStreamServer', create=True):",
                "    delattr(socketserver, 'UnixStreamServer')",
                "    from anneal_lsp import cli",
                "assert not cli._HAS_UNIX_DAEMON",
                "with mock.patch('sys.stderr', new=io.StringIO()):",
                "    assert cli.main(['daemon']) == 1",
                "    assert cli.main(['stop-daemon']) == 1",
                "inp = io.StringIO(json.dumps({'jsonrpc':'2.0','id':1,'method':'shutdown'})+'\\n')",
                "out = io.StringIO()",
                "with mock.patch('sys.stdin', inp), mock.patch('sys.stdout', out):",
                "    assert cli.main(['--no-sandbox', 'mcp']) == 0",
                "assert json.loads(out.getvalue())['id'] == 1",
                "with mock.patch('sys.stdout', new=io.StringIO()):",
                f"    assert cli.main(['--direct', '--no-sandbox', 'outline', {str(ws)!r}]) == 0",
                f"    assert cli.main(['--no-sandbox', 'outline', {str(ws)!r}]) == 0",
            ])
            wp_res = subprocess.run(
                [sys.executable, "-B", "-"], input=win_probe, text=True,
                capture_output=True, timeout=15,
            )
            self.assertEqual(wp_res.returncode, 0, wp_res.stderr)

            # Bound `close()` cleanly even when descendants keep stdout open.
            orphan_script = (
                "import os, pathlib, subprocess, sys, time; "
                "c = subprocess.Popen([sys.executable, '-c', "
                "'import os, time; os.setsid(); time.sleep(10)']); "
                "pathlib.Path(sys.argv[1]).write_text(str(c.pid)); "
                "time.sleep(10)"
            )
            env_path = {"PATH": os.environ.get("PATH", "/usr/bin:/bin")}
            pid_noattr, pid_setsid = root / "gc_noattr.pid", root / "gc_setsid.pid"
            try:
                win_proc = LspProcess([sys.executable, "-c", orphan_script, str(pid_noattr)],
                                      cwd=root, env=env_path)
                dl_pid = time.monotonic() + 5.0
                while not pid_noattr.is_file() and time.monotonic() < dl_pid:
                    time.sleep(0.02)
                self.assertTrue(pid_noattr.is_file())
                w_in, w_out = win_proc.proc.stdin, win_proc.proc.stdout
                fake_os = types.SimpleNamespace(
                    name=os.name, write=os.write, close=os.close, getpgid=os.getpgid,
                )
                fake_sig = types.SimpleNamespace(SIGTERM=signal.SIGTERM)
                t_close = time.monotonic()
                with mock.patch("anneal_lsp.client.os.killpg", None), \
                     mock.patch("anneal_lsp.client.signal.SIGKILL", None):
                    win_proc.close()
                self.assertLess(time.monotonic() - t_close, 2.0)
                self.assertIsNotNone(win_proc.proc.poll())
                self.assertTrue(w_in is not None and w_in.closed)
                self.assertTrue(w_out is not None and w_out.closed)

                noattr_proc = LspProcess(["/bin/sh", "-c", "sleep 10"], cwd=root, env=env_path)
                t_noattr = time.monotonic()
                with mock.patch("anneal_lsp.client.os", fake_os), \
                     mock.patch("anneal_lsp.client.signal", fake_sig):
                    noattr_proc.close()
                self.assertLess(time.monotonic() - t_noattr, 2.0)
                self.assertIsNotNone(noattr_proc.proc.poll())

                setsid_proc = LspProcess([sys.executable, "-c", orphan_script, str(pid_setsid)],
                                         cwd=root, env=env_path)
                dl_sid = time.monotonic() + 5.0
                while not pid_setsid.is_file() and time.monotonic() < dl_sid:
                    time.sleep(0.02)
                self.assertTrue(pid_setsid.is_file())
                t_sid = time.monotonic()
                setsid_proc.close()
                self.assertLess(time.monotonic() - t_sid, 2.0)
                self.assertIsNotNone(setsid_proc.proc.poll())
            finally:
                for pf in (pid_noattr, pid_setsid):
                    if pf.is_file():
                        try:
                            os.kill(int(pf.read_text(encoding="utf-8").strip()), signal.SIGKILL)
                        except (OSError, ValueError):
                            pass

            # Missing Lean fails under ANNEAL_CI_STRICT=1 instead of skipping.
            live_case = LiveLeanServerIntegrationTest(
                "test_live_lean_server_warmth_tools_and_multi_attempt"
            )
            with mock.patch.object(sys.modules[__name__], "_maybe_live_lean", return_value=None):
                with mock.patch.dict(os.environ, {"ANNEAL_CI_STRICT": "1"}, clear=False):
                    with self.assertRaises(AssertionError):
                        live_case.test_live_lean_server_warmth_tools_and_multi_attempt()
                with mock.patch.dict(os.environ, {}, clear=True):
                    with self.assertRaises(unittest.SkipTest):
                        live_case.test_live_lean_server_warmth_tools_and_multi_attempt()

            # Reject shared / non-private socket directories and loose sockets.
            with mock.patch.dict(os.environ, {"ANNEAL_LSP_SOCKET": "/tmp/shared.sock"}):
                with mock.patch("sys.stderr", new=io.StringIO()):
                    self.assertEqual(cli_main(["diag", str(ws / "Demo.lean")]), 1)
            loose_dir = root / "loose_sock_dir"
            loose_dir.mkdir(mode=0o755)
            loose_dir.chmod(0o755)
            with mock.patch.dict(
                os.environ, {"ANNEAL_LSP_SOCKET": str(loose_dir / "lsp.sock")}, clear=False
            ):
                with mock.patch("sys.stderr", new=io.StringIO()):
                    self.assertEqual(cli_main(["diag", str(ws / "Demo.lean")]), 1)
            priv_dir = root / "priv_sock_dir"
            priv_dir.mkdir(mode=0o700)
            bad_sock = priv_dir / "bad.sock"
            bad_srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            bad_srv.bind(str(bad_sock))
            bad_sock.chmod(0o666)
            try:
                with mock.patch.dict(os.environ, {"ANNEAL_LSP_SOCKET": str(bad_sock)}):
                    with mock.patch("sys.stderr", new=io.StringIO()):
                        self.assertEqual(cli_main(["diag", str(ws / "Demo.lean")]), 1)
            finally:
                bad_srv.close()

            eof_sock = root / "eof.sock"
            srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            srv.bind(str(eof_sock))
            srv.listen(1)

            def accept_close() -> None:
                conn, _ = srv.accept()
                conn.recv(1024)
                conn.close()

            th = threading.Thread(target=accept_close, daemon=True)
            th.start()
            try:
                self.assertIsNone(_check_daemon_ping(str(eof_sock), timeout_s=1.0))
            finally:
                srv.close()
                th.join(timeout=2.0)


class MockLspAndMcpTests(unittest.TestCase):
    def _make_mock_lean(self, tmp: Path) -> Path:
        tc = tmp / "mock_tc/bin"
        tc.mkdir(parents=True)
        (tmp / "mock_tc/lib/lean").mkdir(parents=True)
        mock_srv = tc / "mock_srv.py"
        mock_srv.write_text(_MOCK_LSP_SERVER, encoding="utf-8")
        lean_shim = tc / "lean"
        lean_shim.write_text(
            f'#!/usr/bin/env bash\nexec "{sys.executable}" -B "{mock_srv}" "$@"\n',
            encoding="utf-8",
        )
        lean_shim.chmod(0o755)
        return lean_shim

    def test_multi_attempt_hover_lock_free_evict_and_mcp(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean_shim = self._make_mock_lean(root)
            unit = root / "unit"
            unit.mkdir()
            (unit / "request.json").write_text("{}", encoding="utf-8")
            proof = unit / "Proof.lean"
            orig_body = "theorem demo : 1 = 1 := by\n  rfl\n"
            proof.write_text(orig_body, encoding="utf-8")
            orig_mtime = proof.stat().st_mtime_ns
            (unit / "AlphaHelper.lean").write_text("def alphaLemma := 1\n", encoding="utf-8")

            m_env = _scrubbed_env({"ANNEAL_LEAN": str(lean_shim)})
            with mock.patch.dict(os.environ, m_env, clear=True):
                pool = WorkspacePool(max_workers=1, sandbox=False)
                try:
                    cands = [
                        "bad_tac", "header_err", "exact sorryAx _ false",
                        "exact _root_.sorryAx False true", "exact @_root_.sorryAx False true",
                        "exact _root_.«sorryAx» False true", "unsolved_step", "rfl",
                    ]
                    out_ma = pool.multi_attempt(str(proof), 2, cands)
                    att = out_ma["attempts"]
                    self.assertFalse(att[0]["closes_goal"])
                    self.assertEqual(att[1]["errors"][0]["line"], 1)
                    for idx in (2, 3, 4, 5):
                        self.assertTrue(
                            att[idx]["uses_sorry"] and not att[idx]["closes_goal"], att[idx]
                        )
                    self.assertTrue(att[6]["ok_step"] and not att[6]["closes_goal"])
                    self.assertTrue(att[7]["closes_goal"])
                    self.assertIn("advisory", out_ma["text"])

                    with self.assertRaisesRegex(ValueError, "12"):
                        pool.multi_attempt(str(proof), 2, ["rfl"] * 13)

                    # Indented hover/def without symbol skips leading spaces.
                    hv = pool.hover(str(proof), 2)
                    self.assertGreater(hv["column"], 1)
                    self.assertEqual(json.loads(hv["hover"])["col"], 2)
                    df = pool.definition(str(proof), 2)
                    self.assertEqual(df["locations"][0]["column"], 3)

                    # Eviction closes retired worker outside pool._lock.
                    blk = unit / "Blocked.lean"
                    blk.write_text("theorem b : 1 = 1 := by\n  prior_err\n  sorry\n", "utf-8")
                    r_blk = pool.multi_attempt(str(blk), 3, ["rfl"])["attempts"][0]
                    self.assertFalse(r_blk["evaluated"])
                    self.assertEqual(r_blk["errors"][0]["line"], 2)

                    orig_close = next(iter(pool._workers.values())).close
                    lock_states: list[bool] = []
                    with mock.patch.object(
                        next(iter(pool._workers.values())), "close",
                        side_effect=lambda: (lock_states.append(pool._lock.locked()), orig_close()),
                    ):
                        other_dir = root / "other_ws"
                        other_dir.mkdir()
                        (other_dir / "O.lean").write_text("def z := 1\n", encoding="utf-8")
                        pool.diagnostics(str(other_dir / "O.lean"))
                    self.assertEqual(lock_states, [False])

                    secret = root / "credentials.txt"
                    secret.write_text("SECRET=123\n", encoding="utf-8")
                    with self.assertRaises(ValueError):
                        pool.goal(str(secret), 1)
                    bad = unit / "Fatal.lean"
                    bad.write_text(
                        "import Nonexistent\n-- fatal_imp header_err\n", encoding="utf-8"
                    )
                    self.assertTrue(pool.diagnostics(str(bad))["fatal"])
                    g_fatal = pool.goal(str(bad), 2)
                    self.assertIn("fatal", g_fatal["text"].lower())
                    herr = unit / "HeaderErr.lean"
                    herr.write_text("def herr := 1 -- header_err\n", encoding="utf-8")
                    g_herr = pool.goal(str(herr), 1)
                    self.assertIn("file has errors", g_herr["text"].lower())
                    herr.unlink()
                    sr = pool.local_search("regex:^alpha", workspace=str(unit))
                    self.assertTrue(any(m["name"] == "alphaLemma" for m in sr["matches"]))
                    guil_f = unit / "Guillemet.lean"
                    guil_f.write_text("def «my_custom_fn» : Nat := 1\n", encoding="utf-8")
                    out_u = pool.outline(str(unit))
                    self.assertTrue(any(s["name"] == "«my_custom_fn»" for s in out_u["symbols"]))
                    sr_g = pool.local_search("my_custom_fn", workspace=str(unit))
                    self.assertTrue(any(m["name"] == "«my_custom_fn»" for m in sr_g["matches"]))
                    guil_f.unlink()
                    self.assertEqual(proof.read_text(encoding="utf-8"), orig_body)
                    self.assertEqual(proof.stat().st_mtime_ns, orig_mtime)

                    # FIFOs named *.lean never hang outline, search, or def.
                    if hasattr(os, "mkfifo"):
                        fifo_f = unit / "Pipe.lean"
                        os.mkfifo(fifo_f)
                        t_fifo = time.monotonic()
                        self.assertIsInstance(pool.outline(str(unit))["symbols"], list)
                        self.assertIsInstance(
                            pool.local_search("alpha", workspace=str(unit))["matches"], list
                        )
                        fifo_def = unit / "FifoDef.lean"
                        fifo_def.write_text(f"-- def_uri: {fifo_f.as_uri()}\n", encoding="utf-8")
                        fd_res = pool.definition(str(fifo_def), 1)
                        self.assertEqual(fd_res["locations"][0]["snippet"], "")
                        self.assertLess(time.monotonic() - t_fifo, 3.0)
                        fifo_def.unlink()
                        fifo_f.unlink()

                    # Severity filter hides items without zeroing error_count.
                    mix_f = unit / "MixSev.lean"
                    mix_f.write_text(
                        "theorem m_err : 1 = 1 := by\n  bad_tac\n"
                        "theorem m_warn : 1 = 1 := by\n  sorry\n",
                        encoding="utf-8",
                    )
                    d_warn = pool.diagnostics(str(mix_f), severity="warning")
                    self.assertEqual((d_warn["error_count"], d_warn["warning_count"]), (1, 1))
                    self.assertIn("Errors: 1 | Warnings: 1", d_warn["text"])
                    self.assertEqual([x["severity"] for x in d_warn["diagnostics"]], ["warning"])
                    d_err = pool.diagnostics(str(mix_f), severity="error")
                    self.assertEqual((d_err["error_count"], d_err["warning_count"]), (1, 1))
                    self.assertEqual([x["severity"] for x in d_err["diagnostics"]], ["error"])
                    mcp_warn = handle_mcp_request(pool, {
                        "jsonrpc": "2.0", "id": 18, "method": "tools/call",
                        "params": {
                            "name": "lean_diagnostics",
                            "arguments": {"file": str(mix_f), "severity": "warning"},
                        },
                    })
                    assert mcp_warn is not None
                    mcp_warn_txt = mcp_warn["result"]["content"][0]["text"]
                    self.assertIn("Errors: 1 | Warnings: 1", mcp_warn_txt)
                    mix_f.unlink()

                    r_bad = handle_mcp_request(pool, {
                        "jsonrpc": "2.0", "id": 9, "method": "tools/call",
                        "params": {
                            "name": "lean_hover",
                            "arguments": {
                                "file": str(proof), "line": 1, "sandbox": False,
                                "lean_path": [str(unit)],
                            },
                        },
                    })
                    assert r_bad is not None
                    self.assertNotIn(str(unit), r_bad["result"]["content"][0]["text"])

                    # Reject unsupported severity in MCP dispatch and pool API.
                    for bad_sev in ("bogus", "", "info", 123):
                        r_sev = handle_mcp_request(pool, {
                            "jsonrpc": "2.0", "id": 19, "method": "tools/call",
                            "params": {
                                "name": "lean_diagnostics",
                                "arguments": {"file": str(proof), "severity": bad_sev},
                            },
                        })
                        assert r_sev is not None
                        self.assertTrue(r_sev["result"].get("isError"), (bad_sev, r_sev))
                    with self.assertRaises(ValueError):
                        pool.diagnostics(str(proof), severity="bogus")

                    # In-place .olean overwrite restarts worker even with
                    # unchanged lean-lib directory mtime.
                    art_w = root / "art_watch"
                    ll_dir = art_w / "lean-lib"
                    ll_dir.mkdir(parents=True)
                    ol = ll_dir / "Expected.olean"
                    ol.write_bytes(b"v1")
                    d_w1 = pool.diagnostics(str(proof), artifacts_dir=art_w)
                    dir_st, ol_st = ll_dir.stat(), ol.stat()
                    ol.write_bytes(b"v2")
                    os.utime(ol, ns=(ol_st.st_atime_ns, ol_st.st_mtime_ns + 5_000_000))
                    os.utime(ll_dir, ns=(dir_st.st_atime_ns, dir_st.st_mtime_ns))
                    d_w2 = pool.diagnostics(str(proof), artifacts_dir=art_w)
                    self.assertNotEqual(d_w1["server_pid"], d_w2["server_pid"])

                    # Lake workspace without matching lake binary fails loudly.
                    no_lk = root / "no_lake_ws"
                    no_lk.mkdir()
                    (no_lk / "lakefile.toml").write_text('name = "demo"\n', encoding="utf-8")
                    (no_lk / "Demo.lean").write_text("def x := 1\n", encoding="utf-8")
                    self.assertEqual(discover_workspace(no_lk / "Demo.lean").mode, "lake")
                    with self.assertRaisesRegex(FileNotFoundError, "lake"):
                        pool.diagnostics(str(no_lk / "Demo.lean"))

                    # Reject untrusted, symlinked, non-Lean, or hidden defs.
                    ext_secret = root / "outside_secret.txt"
                    ext_secret.write_text("OUTSIDE_SECRET_LINE\n", encoding="utf-8")
                    txt_in_ws = unit / "nested_secret.txt"
                    txt_in_ws.write_text("NON_LEAN_SECRET_LINE\n", encoding="utf-8")
                    sym_def = unit / "SymDef.lean"
                    sym_def.symlink_to(ext_secret)
                    nhome, nxdg, nsock = unit / ".n_home", unit / ".n_xdg", unit / ".n_sock"
                    for hd in (nhome, nxdg, nsock):
                        hd.mkdir(mode=0o700)
                        (hd / "Secret.lean").write_text("NESTED_SECRET_LINE\n", encoding="utf-8")
                    with mock.patch.dict(
                        os.environ, {"XDG_RUNTIME_DIR": str(nxdg)}, clear=False
                    ):
                        hp_pool = WorkspacePool(
                            sandbox=False, hidden_paths=(nsock,),
                        )
                        try:
                            for target_uri, marker in (
                                (ext_secret.as_uri(), "OUTSIDE_SECRET_LINE"),
                                (sym_def.as_uri(), "OUTSIDE_SECRET_LINE"),
                                (txt_in_ws.as_uri(), "NON_LEAN_SECRET_LINE"),
                                ((nhome / "Secret.lean").as_uri(), "NESTED_SECRET_LINE"),
                                ((nxdg / "Secret.lean").as_uri(), "NESTED_SECRET_LINE"),
                                ((nsock / "Secret.lean").as_uri(), "NESTED_SECRET_LINE"),
                            ):
                                probe_def = unit / "ProbeDef.lean"
                                probe_def.write_text(
                                    f"-- def_uri: {target_uri}\n", encoding="utf-8"
                                )
                                d_sec = hp_pool.definition(str(probe_def), 1, caller_home=nhome)
                                self.assertEqual(d_sec["locations"][0]["snippet"], "")
                                self.assertNotIn(marker, d_sec["text"])
                            other_h = root / "other_env_home"
                            other_h.mkdir()
                            probe_def.write_text(
                                f"-- def_uri: {(nhome / 'Secret.lean').as_uri()}\n",
                                encoding="utf-8",
                            )
                            with mock.patch(
                                "pwd.getpwuid", return_value=mock.Mock(pw_dir=str(nhome))
                            ):
                                d_pw = hp_pool.definition(str(probe_def), 1, caller_home=other_h)
                                self.assertEqual(d_pw["locations"][0]["snippet"], "")
                            local_ws = nhome / ".local/ws"
                            local_ws.mkdir(parents=True)
                            (local_ws / "request.json").write_text("{}", encoding="utf-8")
                            local_sp = local_ws / "LocalSpec.lean"
                            local_sp.write_text("def in_local_ws := 1\n", encoding="utf-8")
                            local_main = local_ws / "LocalMain.lean"
                            local_main.write_text(
                                f"-- def_uri: {local_sp.as_uri()}\n", encoding="utf-8"
                            )
                            d_loc = hp_pool.definition(str(local_main), 1, caller_home=nhome)
                            self.assertIn("in_local_ws", d_loc["locations"][0]["snippet"])
                        finally:
                            hp_pool.shutdown()

                    # Remaining admissions in line or decl stay INCOMPLETE.
                    multi_doc = unit / "MultiAdmit.lean"
                    multi_doc.write_text(
                        "theorem two_on_line : 1 = 1 ∧ 2 = 2 := by\n"
                        "  exact ⟨by sorry, by sorry⟩\n"
                        "theorem hidden_macro : 1 = 1 := by\n"
                        "  sorry\n"
                        "theorem isolated_ok : 1 = 1 := by\n"
                        "  sorry\n"
                        "theorem later_sorry : 1 = 1 := by\n"
                        "  sorry\n",
                        encoding="utf-8",
                    )
                    r_pair = pool.multi_attempt(str(multi_doc), 2, ["rfl"])
                    a_pair = r_pair["attempts"][0]
                    self.assertTrue(a_pair["uses_sorry"] and not a_pair["closes_goal"])
                    self.assertIn("INCOMPLETE", r_pair["text"])
                    r_mac = pool.multi_attempt(str(multi_doc), 4, ["hidden_admit_macro"])
                    a_mac = r_mac["attempts"][0]
                    self.assertTrue(a_mac["uses_sorry"] and not a_mac["closes_goal"])
                    self.assertIn("INCOMPLETE", r_mac["text"])
                    r_iso = pool.multi_attempt(str(multi_doc), 6, ["rfl"])["attempts"][0]
                    self.assertTrue(r_iso["closes_goal"] and not r_iso["uses_sorry"])

                    # Multiple sorrys on one line are all counted and queried.
                    pair_diag = pool.diagnostics(str(multi_doc))
                    self.assertEqual(pair_diag["sorry_lines"][:2], [2, 2])
                    self.assertEqual(len(pair_diag["sorry_goals"]), 5)
                    self.assertLess(
                        pair_diag["sorry_goals"][0]["column"],
                        pair_diag["sorry_goals"][1]["column"],
                    )

                    # Propagate sync/RPC timeouts across query tools.
                    w_sync = next(iter(pool._workers.values()))
                    with mock.patch.object(
                        w_sync, "sync_text", return_value=(proof.as_uri(), 5.0, False)
                    ):
                        with mock.patch.object(
                            w_sync.lsp, "request", side_effect=AssertionError("unexpected RPC")
                        ):
                            g_to = pool.goal(str(proof), 2)
                            hv_to = pool.hover(str(proof), 2)
                            df_to = pool.definition(str(proof), 2)
                            cp_to = pool.completions(str(proof), 2)
                            ol_to = pool.outline(str(proof))
                    self.assertTrue(g_to["timed_out"] and not g_to["completed"])
                    self.assertIn("timed out", g_to["text"].lower())
                    self.assertNotIn("no tactic goals", g_to["text"])
                    self.assertNotIn("no goals", g_to["text"])
                    for res_to in (hv_to, df_to, cp_to, ol_to):
                        self.assertTrue(res_to["timed_out"] and not res_to["completed"])
                        self.assertIn("timed out", res_to["text"].lower())
                    self.assertNotIn("No hover info", hv_to["text"])
                    self.assertNotIn("No definition", df_to["text"])
                    self.assertNotIn("No completions", cp_to["text"])
                    with mock.patch.object(
                        w_sync, "sync_text", return_value=(proof.as_uri(), 5.0, True)
                    ):
                        with mock.patch.object(
                            w_sync.lsp, "request", side_effect=TimeoutError("timed out")
                        ):
                            self.assertTrue(pool.goal(str(proof), 2)["timed_out"])
                            self.assertTrue(pool.hover(str(proof), 2)["timed_out"])
                            self.assertTrue(pool.definition(str(proof), 2)["timed_out"])
                            self.assertTrue(pool.completions(str(proof), 2)["timed_out"])
                            self.assertTrue(pool.outline(str(proof))["timed_out"])
                    with mock.patch.object(
                        pool, "_goal_at", side_effect=TimeoutError("timed out")
                    ):
                        ma_to = pool.multi_attempt(str(proof), 2, ["rfl"])
                        diag_gto = pool.diagnostics(str(multi_doc))
                    self.assertTrue(ma_to["attempts"][0]["timed_out"])
                    self.assertFalse(ma_to["attempts"][0]["closes_goal"])
                    self.assertFalse(ma_to["attempts"][0]["ok_step"])
                    self.assertIn("TIMEOUT", ma_to["text"])
                    self.assertTrue(diag_gto["timed_out"] and not diag_gto["completed"])
                    self.assertTrue(diag_gto["sorry_goals"][0]["timed_out"])
                    self.assertIn("timed out", diag_gto["text"].lower())
                    ma_bgt = pool.multi_attempt(
                        str(proof), 2, ["rfl", "simp"], candidate_budget_s=0.0
                    )
                    self.assertTrue(all(a["timed_out"] for a in ma_bgt["attempts"]))

                    # Editing imported sibling restarts unchanged Main worker.
                    lib_f, main_f = unit / "DepLib.lean", unit / "DepMain.lean"
                    lib_f.write_text("def dv : Nat := 1\n", encoding="utf-8")
                    main_f.write_text("import DepLib\n-- m1\n", encoding="utf-8")
                    dm1 = pool.diagnostics(str(main_f))
                    dm1_again = pool.diagnostics(str(main_f))
                    self.assertEqual(dm1["server_pid"], dm1_again["server_pid"])
                    lib_st = lib_f.stat()
                    lib_f.write_text("def dv : Nat := 2\n", encoding="utf-8")
                    os.utime(lib_f, ns=(lib_st.st_atime_ns, lib_st.st_mtime_ns + 5_000_000))
                    dm2 = pool.diagnostics(str(main_f))
                    self.assertNotEqual(dm1["server_pid"], dm2["server_pid"])
                    main_f.write_text("import DepLib\n-- m2\n", encoding="utf-8")
                    dm3 = pool.diagnostics(str(main_f))
                    self.assertEqual(dm2["server_pid"], dm3["server_pid"])

                    # Malformed frame marks LspProcess dead and replaces worker.
                    w_live = next(iter(pool._workers.values()))
                    old_pid = w_live.lsp.proc.pid
                    bad_proc = LspProcess(
                        [sys.executable, "-c",
                         "import sys,time; sys.stdout.write('Content-Length: 4\\r\\n\\r\\n{bad');"
                         " sys.stdout.flush(); time.sleep(30)"],
                        cwd=unit, env={"PATH": os.environ.get("PATH", "/usr/bin:/bin")},
                    )
                    try:
                        with self.assertRaises(RuntimeError):
                            bad_proc.request("initialize", {}, 5.0)
                        deadline = time.monotonic() + 3.0
                        while bad_proc.is_alive() and time.monotonic() < deadline:
                            time.sleep(0.02)
                        self.assertFalse(bad_proc.is_alive())
                    finally:
                        bad_proc.close()
                    w_live.lsp._closed = True
                    d_respawn = pool.diagnostics(str(proof))
                    self.assertNotEqual(d_respawn["server_pid"], old_pid)

                    # Wait for delayed publishDiagnostics + fallback on -32601.
                    del_f = unit / "Delayed.lean"
                    del_f.write_text("-- delay_diag\ndef d := 1\n", encoding="utf-8")
                    del_d = pool.diagnostics(str(del_f))
                    self.assertTrue(del_d["completed"])
                    self.assertEqual(del_d["error_count"], 1)
                    self.assertIn("delayed diagnostic", del_d["text"])
                    wfd_f = unit / "NoWfd.lean"
                    wfd_f.write_text("-- unsupported_wfd\n  bad_tac\n", encoding="utf-8")
                    wfd_d = pool.diagnostics(str(wfd_f))
                    self.assertTrue(wfd_d["completed"] and wfd_d["error_count"] == 1)

                    # Retry unchanged doc sync after prior wait timeout.
                    retry_f = unit / "RetrySync.lean"
                    retry_f.write_text("def r_ok := 1\n", encoding="utf-8")
                    w_r = next(iter(pool._workers.values()))
                    orig_wait = w_r._wait_ready

                    def fail_once(u: str, v: int, sq: int, tm: float) -> bool:
                        with w_r._cond:
                            w_r._prog[u] = (v, [])
                        return False

                    with mock.patch.object(w_r, "_wait_ready", side_effect=fail_once):
                        r1 = pool.diagnostics(str(retry_f))
                    self.assertFalse(r1["completed"])
                    with mock.patch.object(
                        w_r, "_wait_ready", wraps=orig_wait
                    ) as wait_spy:
                        r2 = pool.diagnostics(str(retry_f))
                        self.assertEqual(wait_spy.call_count, 1)
                        self.assertTrue(r2["completed"])
                        r3 = pool.diagnostics(str(retry_f))
                        self.assertEqual(wait_spy.call_count, 1)
                        self.assertTrue(r3["completed"])

                    # Non--32601 waitForDiagnostics error avoids 10s hangs.
                    crash_f = unit / "CrashMock.lean"
                    crash_f.write_text(
                        "-- crash_wfd\ntheorem cr : 1 = 1 := by\n  sorry\n", encoding="utf-8"
                    )
                    d_cr = pool.diagnostics(str(crash_f))
                    self.assertFalse(d_cr["completed"])
                    self.assertFalse(d_cr["timed_out"])
                    self.assertGreaterEqual(d_cr["error_count"], 1)
                    self.assertEqual(d_cr["sorry_goals"], [])
                    g_cr = pool.goal(str(crash_f), 2)
                    self.assertFalse(g_cr["completed"] or g_cr["timed_out"])
                    self.assertLess(g_cr["elapsed_ms"], 2000.0)
                    h_cr = pool.hover(str(crash_f), 2)
                    self.assertFalse(h_cr["completed"] or h_cr["timed_out"])
                    ma_cr = pool.multi_attempt(str(crash_f), 3, ["rfl"])
                    self.assertFalse(ma_cr["attempts"][0]["evaluated"])
                    crash_f.write_text("theorem cr : 1 = 1 := by\n  sorry\n", encoding="utf-8")
                    d_rec = pool.diagnostics(str(crash_f))
                    self.assertTrue(d_rec["completed"] and not d_rec["timed_out"])
                    self.assertEqual(d_rec["error_count"], 0)
                    self.assertTrue(
                        pool.multi_attempt(str(crash_f), 2, ["rfl"])["attempts"][0]["closes_goal"]
                    )

                    # Dropped waitForDiagnostics after fatalError stops cleanly.
                    drop_f = unit / "DropWfd.lean"
                    drop_f.write_text(
                        "-- drop_wfd\ntheorem dr : 1 = 1 := by\n  sorry\n", encoding="utf-8"
                    )
                    d_dw = pool.diagnostics(str(drop_f))
                    self.assertFalse(d_dw["completed"] or d_dw["timed_out"])
                    self.assertGreaterEqual(d_dw["error_count"], 1)
                    self.assertLess(d_dw["elapsed_ms"], 3000.0)
                    g_dw = pool.goal(str(drop_f), 2)
                    self.assertFalse(g_dw["completed"] or g_dw["timed_out"])
                    self.assertLess(g_dw["elapsed_ms"], 2000.0)
                    h_dw = pool.hover(str(drop_f), 2)
                    self.assertFalse(h_dw["completed"] or h_dw["timed_out"])
                    self.assertFalse(
                        pool.multi_attempt(str(drop_f), 3, ["rfl"])["attempts"][0]["evaluated"]
                    )
                    drop_f.write_text("theorem dr : 1 = 1 := by\n  rfl\n", encoding="utf-8")
                    d_dw_ok = pool.diagnostics(str(drop_f))
                    self.assertTrue(d_dw_ok["completed"] and d_dw_ok["error_count"] == 0)

                    # Do not leak stale diags or fatal progress across versions.
                    stale_f = unit / "StaleVer.lean"
                    stale_f.write_text("theorem sv : 1 = 1 := by\n  sorry\n", encoding="utf-8")
                    ma_st = pool.multi_attempt(
                        str(stale_f), 2, ["bad_tac", "crash_wfd", "sorry", "drop_wfd"],
                    )["attempts"]
                    self.assertIn("bad_tac", ma_st[0]["errors"][0]["message"])
                    self.assertNotIn("bad_tac", ma_st[1]["errors"][0]["message"])
                    self.assertIn("waitForDiagnostics", ma_st[1]["errors"][0]["message"])
                    self.assertTrue(ma_st[2]["uses_sorry"])
                    self.assertFalse(ma_st[3]["uses_sorry"])
                    self.assertIn("waitForDiagnostics", ma_st[3]["errors"][0]["message"])

                    stale_diag = unit / "StaleDiag.lean"
                    stale_diag.write_text("theorem sd : 1 = 1 := by\n  bad_tac\n", "utf-8")
                    sd1 = pool.diagnostics(str(stale_diag))
                    self.assertEqual(sd1["error_count"], 1)
                    w_sd = next(iter(pool._workers.values()))
                    sd_uri = stale_diag.as_uri()
                    w_sd._on_notify("textDocument/publishDiagnostics", {
                        "uri": sd_uri, "version": 0,
                        "diagnostics": [{"severity": 1, "message": "old",
                                         "range": {"start": {"line": 0, "character": 0},
                                                   "end": {"line": 0, "character": 1}}}],
                    })
                    self.assertEqual(len(w_sd.diags(sd_uri)), 1)
                    self.assertIn("bad_tac", w_sd.diags(sd_uri)[0]["message"])
                    with w_sd._cond:
                        w_sd._prog[sd_uri] = (0, [{"kind": 2}])
                    self.assertFalse(w_sd.has_fatal_progress(sd_uri))
                    stale_diag.write_text(
                        "-- drop_wfd\ntheorem sd : 1 = 1 := by\n  sorry\n", "utf-8"
                    )
                    sd2 = pool.diagnostics(str(stale_diag))
                    self.assertFalse(sd2["completed"])
                    self.assertFalse(any("bad_tac" in d["message"] for d in sd2["diagnostics"]))

                    # Recover cleanly when LSP worker dies mid-multi_attempt.
                    exit_f = unit / "ExitMa.lean"
                    exit_f.write_text("theorem ex_ma : 1 = 1 := by\n  sorry\n", "utf-8")
                    ma_die = pool.multi_attempt(
                        str(exit_f), 2, ["rfl", "exit_on_prog", "sorry"],
                    )
                    att_die = ma_die["attempts"]
                    self.assertTrue(att_die[0]["closes_goal"])
                    self.assertTrue(att_die[1]["evaluated"] and not att_die[1]["ok_step"])
                    self.assertFalse(att_die[1]["timed_out"])
                    self.assertIn("exited", att_die[1]["errors"][0]["message"].lower())
                    self.assertFalse(att_die[2]["evaluated"])
                    self.assertIn("exited", att_die[2]["errors"][0]["message"].lower())
                    self.assertTrue(pool.diagnostics(str(proof))["completed"])

                    ma_die_one = pool.multi_attempt(str(exit_f), 2, ["exit_on_prog"])
                    d_one_att = ma_die_one["attempts"][0]
                    self.assertTrue(d_one_att["evaluated"])
                    self.assertFalse(d_one_att["timed_out"])
                    self.assertIn("exited", d_one_att["errors"][0]["message"].lower())

                    for goal_exc, msg_frag in (
                        (RuntimeError("LSP process is not running"), "not running"),
                        (LspRpcError("$/lean/plainGoal", -32603, "file worker crashed"), "crashed"),
                    ):
                        with mock.patch.object(pool, "_goal_at", side_effect=goal_exc):
                            ma_gd = pool.multi_attempt(str(exit_f), 2, ["rfl"])
                        att_gd = ma_gd["attempts"][0]
                        self.assertFalse(att_gd["ok_step"] or att_gd["timed_out"])
                        self.assertIn(msg_frag, att_gd["errors"][0]["message"])
                        self.assertNotIn("TIMEOUT", ma_gd["text"])

                    # Alive child closing fd 0 or killed reports error cleanly.
                    bp_script = root / "bp_lsp_srv.py"
                    bp_script.write_text(
                        "import json, os, signal, sys, time\n"
                        "while True:\n"
                        "    hdr = {}\n"
                        "    while True:\n"
                        "        ln = sys.stdin.buffer.readline()\n"
                        "        if not ln: sys.exit(0)\n"
                        "        if ln in (b'\\r\\n', b'\\n'): break\n"
                        "        k, v = ln.decode().split(':', 1)\n"
                        "        hdr[k.strip().lower()] = v.strip()\n"
                        "    msg = json.loads(sys.stdin.buffer.read(int(hdr['content-length'])))\n"
                        "    m, rid = msg.get('method'), msg.get('id')\n"
                        "    if m == 'initialize':\n"
                        "        res = json.dumps({'jsonrpc': '2.0', 'id': rid, "
                        "'result': {'capabilities': {}}}).encode()\n"
                        "        sys.stdout.buffer.write(f'Content-Length: {len(res)}\\r\\n\\r\\n'"
                        ".encode() + res)\n"
                        "        sys.stdout.buffer.flush()\n"
                        "    elif m == 'textDocument/didOpen':\n"
                        "        txt = msg['params']['textDocument']['text']\n"
                        "        if 'open_epipe' in txt:\n"
                        "            os.close(0); time.sleep(2.0); break\n"
                        "        if 'kill_wfd' in txt:\n"
                        "            os.kill(os.getpid(), signal.SIGKILL)\n"
                        "        u, v = msg['params']['textDocument']['uri'], "
                        "msg['params']['textDocument']['version']\n"
                        "        n1 = json.dumps({'jsonrpc': '2.0', 'method': "
                        "'textDocument/publishDiagnostics', 'params': {'uri': u, 'version': v, "
                        "'diagnostics': []}}).encode()\n"
                        "        sys.stdout.buffer.write(f'Content-Length: {len(n1)}\\r\\n\\r\\n'"
                        ".encode() + n1)\n"
                        "        sys.stdout.buffer.flush()\n"
                        "    elif m == 'textDocument/didChange':\n"
                        "        os.close(0); time.sleep(2.0); break\n"
                        "    elif m == 'textDocument/waitForDiagnostics':\n"
                        "        res = json.dumps({'jsonrpc': '2.0', 'id': rid, "
                        "'result': {}}).encode()\n"
                        "        sys.stdout.buffer.write(f'Content-Length: {len(res)}\\r\\n\\r\\n'"
                        ".encode() + res)\n"
                        "        sys.stdout.buffer.flush()\n",
                        encoding="utf-8",
                    )
                    bp_lean = root / "bp_lean/bin/lean"
                    bp_lean.parent.mkdir(parents=True)
                    bp_lean.write_text(
                        f'#!/bin/sh\nexec "{sys.executable}" -I -B "{bp_script}" "$@"\n',
                        encoding="utf-8",
                    )
                    bp_lean.chmod(0o755)
                    bp_ws = root / "bp_ws"
                    bp_ws.mkdir()
                    (bp_ws / "request.json").write_text("{}", encoding="utf-8")
                    bp_open = bp_ws / "BpOpen.lean"
                    bp_open.write_text("-- open_epipe\ntheorem bo : 1 = 1 := by\n  sorry\n",
                                       encoding="utf-8")
                    bp_kill = bp_ws / "BpKill.lean"
                    bp_kill.write_text("-- kill_wfd\ntheorem bk : 1 = 1 := by\n  sorry\n",
                                       encoding="utf-8")
                    bp_f = bp_ws / "Bp.lean"
                    bp_f.write_text("theorem bp : 1 = 1 := by\n  sorry\n", encoding="utf-8")
                    with mock.patch.dict(
                        os.environ, _scrubbed_env({"ANNEAL_LEAN": str(bp_lean)}), clear=True,
                    ):
                        bp_pool = WorkspacePool(sandbox=False)
                        try:
                            bp_d = bp_pool.diagnostics(str(bp_open))
                            self.assertFalse(bp_d["completed"] or bp_d["timed_out"])
                            self.assertGreaterEqual(bp_d["error_count"], 1)
                            bp_kd = bp_pool.diagnostics(str(bp_kill))
                            self.assertFalse(bp_kd["completed"] or bp_kd["timed_out"])
                            self.assertGreaterEqual(bp_kd["error_count"], 1)
                            self.assertIn("exited", bp_kd["text"].lower())
                            for k_res in (
                                bp_pool.goal(str(bp_kill), 2),
                                bp_pool.hover(str(bp_kill), 2),
                                bp_pool.outline(str(bp_kill)),
                            ):
                                self.assertFalse(k_res["completed"] or k_res["timed_out"])
                                self.assertIn("exited", k_res["text"].lower())
                            bp_ma = bp_pool.multi_attempt(str(bp_f), 2, ["rfl", "simp"])
                            self.assertFalse(bp_ma["attempts"][0]["timed_out"])
                            self.assertGreaterEqual(len(bp_ma["attempts"][0]["errors"]), 1)
                            self.assertFalse(bp_ma["attempts"][1]["evaluated"])
                        finally:
                            bp_pool.shutdown()

                    # Child exit during post-progress wait fails wait_ready.
                    die_f = unit / "DieProg.lean"
                    die_f.write_text("-- exit_on_prog\ndef z := 1\n", encoding="utf-8")
                    d_die = pool.diagnostics(str(die_f))
                    self.assertFalse(d_die["completed"])
                    self.assertTrue(d_die["timed_out"])

                    # Interpolated holes and string gaps preserve sorry lines.
                    interp_f = unit / "Interp.lean"
                    interp_f.write_text(
                        'def g := "a\\\n  b"\n'
                        'def h := s!"x {(sorry : Nat)}"\n',
                        encoding="utf-8",
                    )
                    interp_d = pool.diagnostics(str(interp_f))
                    self.assertEqual(interp_d["sorry_lines"], [3])

                    # Enforce `max_workers` under concurrent multi-root load.
                    ws_c1, ws_c2 = root / "conc_1", root / "conc_2"
                    ws_c1.mkdir()
                    ws_c2.mkdir()
                    (ws_c1 / "request.json").write_text("{}", encoding="utf-8")
                    (ws_c2 / "request.json").write_text("{}", encoding="utf-8")
                    (ws_c1 / "C1.lean").write_text("-- delay_diag\ndef c1 := 1\n", "utf-8")
                    (ws_c2 / "C2.lean").write_text("def c2 := 1\n", "utf-8")
                    from anneal_lsp.workspace import WorkspaceWorker  # noqa: E402
                    live_n, peak_n, n_lock = 0, 0, threading.Lock()
                    orig_init, orig_wclose = WorkspaceWorker.__init__, WorkspaceWorker.close

                    def tracked_init(wself: Any, *a: Any, **kw: Any) -> None:
                        nonlocal live_n, peak_n
                        orig_init(wself, *a, **kw)
                        with n_lock:
                            live_n += 1
                            peak_n = max(peak_n, live_n)

                    def tracked_close(wself: Any) -> None:
                        nonlocal live_n
                        was_closed = getattr(wself, "_closed", False)
                        orig_wclose(wself)
                        if not was_closed:
                            with n_lock:
                                live_n -= 1

                    with mock.patch.object(WorkspaceWorker, "__init__", tracked_init), \
                         mock.patch.object(WorkspaceWorker, "close", tracked_close):
                        conc_pool = WorkspacePool(max_workers=1, sandbox=False)
                        try:
                            with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
                                f1 = ex.submit(conc_pool.diagnostics, str(ws_c1 / "C1.lean"))
                                time.sleep(0.05)
                                f2 = ex.submit(conc_pool.diagnostics, str(ws_c2 / "C2.lean"))
                                self.assertTrue(f1.result(timeout=15)["completed"])
                                self.assertTrue(f2.result(timeout=15)["completed"])
                        finally:
                            conc_pool.shutdown()
                    self.assertEqual(peak_n, 1)
                    self.assertEqual(live_n, 0)

                    # At max_workers=3, a 4th worker evicts ONLY oldest LRU.
                    lru_dirs = [root / f"lru_{idx}" for idx in range(4)]
                    for ld in lru_dirs:
                        ld.mkdir()
                        (ld / "request.json").write_text("{}", encoding="utf-8")
                        (ld / "L.lean").write_text("def lru := 1\n", encoding="utf-8")
                    lru_pool = WorkspacePool(max_workers=3, sandbox=False)
                    try:
                        pid_at = lambda i: lru_pool.diagnostics(str(lru_dirs[i] / "L.lean"))[
                            "server_pid"
                        ]
                        p0, p1, p2 = pid_at(0), pid_at(1), pid_at(2)
                        _ = pid_at(3)
                        self.assertEqual(len(lru_pool._workers), 3)
                        self.assertEqual(pid_at(1), p1)
                        self.assertEqual(pid_at(2), p2)
                        self.assertNotEqual(pid_at(0), p0)
                    finally:
                        lru_pool.shutdown()

                    # Symlinked Lean target rejected across pool and MCP calls.
                    sym_tgt = unit / "TargetLink.lean"
                    sym_tgt.symlink_to(ext_secret)
                    with self.assertRaises(PermissionError):
                        pool.diagnostics(str(sym_tgt))
                    with self.assertRaises(PermissionError):
                        pool.outline(str(sym_tgt))

                    # Preserve empty file and trailing blank line for positions.
                    empty_f = unit / "Empty.lean"
                    empty_f.write_text("", encoding="utf-8")
                    self.assertEqual(pool.completions(str(empty_f), 1)["items"][0]["label"], "rfl")
                    self.assertEqual(pool.hover(str(empty_f), 1)["line"], 1)
                    trail_f = unit / "Trail.lean"
                    trail_f.write_text("def t := 1\n", encoding="utf-8")
                    self.assertEqual(pool.completions(str(trail_f), 2)["items"][0]["label"], "rfl")
                    self.assertEqual(pool.goal(str(trail_f), 2)["line"], 2)

                    # Counter-offer newest protocolVersion when unknown.
                    init_resp = handle_mcp_request(pool, {
                        "jsonrpc": "2.0", "id": 77, "method": "initialize",
                        "params": {"protocolVersion": "2099-01-01"},
                    })
                    assert init_resp is not None
                    self.assertEqual(init_resp["result"]["protocolVersion"], "2025-06-18")

                    # Honor CLI --artifacts and --lean-path in MCP mode.
                    cli_art = root / "cli_art"
                    (cli_art / "lean-lib").mkdir(parents=True)
                    cli_lp = root / "cli_extra_lp"
                    cli_lp.mkdir()
                    mcp_in = io.StringIO("\n".join([
                        json.dumps({"jsonrpc": "2.0", "id": 1, "method": "tools/call",
                                    "params": {"name": "lean_hover",
                                               "arguments": {"file": str(proof), "line": 1}}}),
                        json.dumps({"jsonrpc": "2.0", "id": 2, "method": "shutdown"}),
                    ]) + "\n")
                    mcp_out = io.StringIO()
                    with mock.patch("sys.stdin", mcp_in), mock.patch("sys.stdout", mcp_out):
                        self.assertEqual(
                            cli_main(["--no-sandbox", "--artifacts", str(cli_art),
                                      "--lean-path", str(cli_lp), "mcp"]),
                            0,
                        )
                    mcp_res = [json.loads(x) for x in mcp_out.getvalue().splitlines() if x.strip()]
                    hv_lp = json.loads(mcp_res[0]["result"]["content"][0]["text"])["lean_path"]
                    self.assertIn(str((cli_art / "lean-lib").resolve()), hv_lp)
                    self.assertIn(str(cli_lp.resolve()), hv_lp)

                    calls = [
                        ("lean_diagnostics", {"file": str(proof)}),
                        ("lean_diagnostics", {"file": str(multi_doc)}),
                        ("lean_goal", {"file": str(proof), "line": 2}),
                        ("lean_multi_attempt", {"file": str(proof), "line": 2, "tactics": ["rfl"]}),
                        ("lean_hover", {"file": str(proof), "line": 1}),
                        ("lean_definition", {"file": str(proof), "line": 1}),
                        ("lean_completions", {"file": str(proof), "line": 1}),
                        ("lean_outline", {"file": str(proof)}),
                        ("lean_local_search", {"query": "alpha", "workspace": str(unit)}),
                        ("lean_restart_workspace", {"root": "all"}),
                    ]
                    inp = io.StringIO("\n".join([
                        json.dumps({"jsonrpc": "2.0", "id": 1, "method": "initialize",
                                    "params": {"protocolVersion": "2025-03-26"}}),
                        json.dumps([1, 2]),
                        json.dumps({"jsonrpc": "2.0", "id": 2, "method": "tools/list"}),
                        *(json.dumps({"jsonrpc": "2.0", "id": i, "method": "tools/call",
                                      "params": {"name": n, "arguments": a}})
                          for i, (n, a) in enumerate(calls, 10)),
                        "[" * 200 + "]",
                        "9" * 5000,
                        json.dumps({"jsonrpc": "2.0", "id": 99, "method": "shutdown"}),
                    ]) + "\n")
                    out = io.StringIO()
                    self.assertEqual(serve_mcp(pool, stdin=inp, stdout=out), 0)
                    resps = [json.loads(ln) for ln in out.getvalue().splitlines() if ln.strip()]
                    self.assertEqual(len(resps), 16)
                    self.assertEqual(len(resps[2]["result"]["tools"]), 9)
                    for r in resps[3:13]:
                        self.assertFalse(r["result"].get("isError"), r)
                    self.assertIn("⊢ 1 = 1", resps[4]["result"]["content"][0]["text"])
                    self.assertEqual(resps[13]["error"]["code"], -32700)
                    self.assertEqual(resps[14]["error"]["code"], -32700)
                    self.assertEqual(resps[15]["id"], 99)
                    for bad_name, bad_args in (
                        ("lean_local_search", {"query": "alpha", "max_results": 0}),
                        ("lean_hover", {"file": str(proof), "line": 1, "column": True}),
                    ):
                        bad_r = handle_mcp_request(pool, {
                            "jsonrpc": "2.0", "id": 100, "method": "tools/call",
                            "params": {"name": bad_name, "arguments": bad_args},
                        })
                        assert bad_r is not None
                        self.assertTrue(bad_r["result"]["isError"])
                    str_col = handle_mcp_request(pool, {
                        "jsonrpc": "2.0", "id": 101, "method": "tools/call",
                        "params": {
                            "name": "lean_hover",
                            "arguments": {"file": str(proof), "line": 1, "column": "3"},
                        },
                    })
                    assert str_col is not None
                    self.assertEqual(json.loads(str_col["result"]["content"][0]["text"])["col"], 2)
                    # Per-tool MCP schema strips unrelated keys like `snippet`.
                    cross_arg = handle_mcp_request(pool, {
                        "jsonrpc": "2.0", "id": 102, "method": "tools/call",
                        "params": {
                            "name": "lean_hover",
                            "arguments": {
                                "file": str(proof), "line": 1, "column": 3,
                                "snippet": "NONEXISTENT_SNIPPET",
                            },
                        },
                    })
                    assert cross_arg is not None and not cross_arg["result"].get("isError")
                    col_v = json.loads(cross_arg["result"]["content"][0]["text"])["col"]
                    self.assertEqual(col_v, 2)
                    for bad_raw in ([], "", 0, False):
                        bad_t = handle_mcp_request(pool, {
                            "jsonrpc": "2.0", "id": 103, "method": "tools/call",
                            "params": {"name": "lean_restart_workspace", "arguments": bad_raw},
                        })
                        assert bad_t is not None and bad_t["result"].get("isError")
                    # Non-POSIX default_socket_path checks daemon flag first.
                    with mock.patch("anneal_lsp.cli._HAS_UNIX_DAEMON", False), \
                         mock.patch("os.getuid", side_effect=AssertionError("os.getuid called")):
                        with self.assertRaises(OSError):
                            default_socket_path()
                    # Non-ASCII ANNEAL_LSP_MEMORY_MB falls back cleanly.
                    sup_inp = io.StringIO(
                        json.dumps({"jsonrpc": "2.0", "id": 1, "method": "shutdown"}) + "\n"
                    )
                    with mock.patch.dict(
                        os.environ, {"ANNEAL_LSP_MEMORY_MB": "\u00b2"}, clear=False
                    ), mock.patch("sys.stdin", sup_inp), \
                         mock.patch("sys.stdout", new=io.StringIO()):
                        self.assertEqual(cli_main(["--no-sandbox", "mcp"]), 0)
                    with mock.patch.dict(
                        os.environ,
                        _scrubbed_env({
                            "ANNEAL_LEAN": str(lean_shim), "ANNEAL_LSP_MEMORY_MB": "\u00b2",
                        }),
                        clear=True,
                    ), mock.patch("sys.stdout", new=io.StringIO()):
                        self.assertEqual(
                            cli_main(["--direct", "--no-sandbox", "hover", str(proof), "1"]), 0
                        )
                    # Explicit --artifacts / artifacts_dir beats env var.
                    ov_a, ov_b = root / "ov_art_a", root / "ov_art_b"
                    (ov_a / "lean-lib").mkdir(parents=True)
                    (ov_b / "lean-lib").mkdir(parents=True)
                    (ov_a / "lean-lib/Expected.olean").write_bytes(b"")
                    ov_env = _scrubbed_env({
                        "ANNEAL_LEAN": str(lean_shim),
                        "ANNEAL_LSP_ARTIFACTS": str(ov_a),
                    })
                    dir_buf = io.StringIO()
                    with mock.patch.dict(os.environ, ov_env, clear=True), \
                         mock.patch("sys.stdout", dir_buf):
                        rc_ov = cli_main([
                            "--json", "--direct", "--no-sandbox",
                            "--artifacts", str(ov_b), "hover", str(proof), "1",
                        ])
                        self.assertEqual(rc_ov, 0)
                        mcp_ov = handle_mcp_request(pool, {
                            "jsonrpc": "2.0", "id": 104, "method": "tools/call",
                            "params": {
                                "name": "lean_hover",
                                "arguments": {
                                    "file": str(proof), "line": 1, "artifacts_dir": str(ov_b),
                                },
                            },
                        })
                    dir_lp = json.loads(json.loads(dir_buf.getvalue())["hover"])["lean_path"]
                    self.assertIn(str(ov_b), dir_lp)
                    self.assertNotIn(str(ov_a), dir_lp)
                    assert mcp_ov is not None
                    mcp_lp = json.loads(mcp_ov["result"]["content"][0]["text"])["lean_path"]
                    self.assertIn(str(ov_b), mcp_lp)
                    self.assertNotIn(str(ov_a), mcp_lp)
                    with mock.patch.dict(
                        os.environ,
                        _scrubbed_env({
                            "ANNEAL_LEAN": str(lean_shim),
                            "ANNEAL_LSP_ARTIFACTS": str(root / "missing_art_dir"),
                        }),
                        clear=True,
                    ), mock.patch("sys.stdout", new=io.StringIO()):
                        self.assertEqual(
                            cli_main([
                                "--json", "--direct", "--no-sandbox",
                                "--artifacts", str(ov_b), "hover", str(proof), "1",
                            ]),
                            0,
                        )
                finally:
                    pool.shutdown()

    def test_daemon_warmth_env_isolation_and_rapid_restart(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            lean_shim = self._make_mock_lean(root)
            (root / "sub").mkdir()
            (root / "sub/Main.lean").write_text("theorem x : 1 = 1 := by\n  sorry\n", "utf-8")
            (root / "art_a/lean-lib").mkdir(parents=True)
            (root / "art_b/lean-lib").mkdir(parents=True)
            sock, entry = str(root / "sockdir/lsp.sock"), str(_CI_DIR / "anneal-lsp")
            base_env = _scrubbed_env({
                "ANNEAL_LEAN": str(lean_shim), "ANNEAL_LSP_SOCKET": sock,
                "ANNEAL_LSP_NO_SANDBOX": "1",
            })

            def run_cmd(args: list[str], env: dict[str, str]) -> dict[str, object]:
                out = subprocess.check_output(
                    [sys.executable, "-B", entry, "--json", *args],
                    cwd=str(root), text=True, env=env, timeout=20,
                )
                return json.loads(out)

            try:
                env_a = {**base_env, "ANNEAL_LSP_ARTIFACTS": str(root / "art_a")}
                env_b = {**base_env, "ANNEAL_LSP_ARTIFACTS": str(root / "art_b")}
                with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
                    res_a = list(
                        ex.map(lambda _: run_cmd(["diag", "sub/Main.lean"], env_a), range(4))
                    )
                self.assertEqual(len({r["server_pid"] for r in res_a}), 1)
                h_base = str(run_cmd(["hover", "sub/Main.lean", "1"], base_env)["hover"])
                self.assertNotIn("art_a", h_base)
                h_b = str(run_cmd(["hover", "sub/Main.lean", "1"], env_b)["hover"])
                self.assertIn("art_b", h_b)
                home2 = root / "caller2_home"
                home2.mkdir()
                h2 = run_cmd(["hover", "sub/Main.lean", "1"], {**base_env, "HOME": str(home2)})
                self.assertEqual(json.loads(str(h2["hover"]))["home"], str(home2.resolve()))

                # Rapid stop-daemon + immediate respawn cycles.
                for _ in range(3):
                    subprocess.check_call(
                        [sys.executable, "-B", entry, "stop-daemon"], env=base_env, timeout=10
                    )
                    d_new = run_cmd(["diag", "sub/Main.lean"], base_env)
                    self.assertTrue(d_new["completed"])

                # Active daemon handlers drain cleanly before exit & reap.
                (root / "sub/Slow.lean").write_text(
                    "-- slow_hover\ndef sh := 1\n", encoding="utf-8"
                )
                d_warm = run_cmd(["diag", "sub/Slow.lean"], base_env)
                lean_pid = int(d_warm["server_pid"])
                with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
                    fut = ex.submit(run_cmd, ["hover", "sub/Slow.lean", "1"], base_env)
                    time.sleep(0.15)
                    subprocess.check_call(
                        [sys.executable, "-B", entry, "stop-daemon"], env=base_env, timeout=10
                    )
                    hv_slow = fut.result(timeout=10)
                self.assertIn("lean_path", str(hv_slow["hover"]))
                with self.assertRaises(ProcessLookupError):
                    os.kill(lean_pid, 0)
            finally:
                subprocess.run(
                    [sys.executable, "-B", entry, "stop-daemon"],
                    env=base_env, check=False, timeout=10,
                )

            # Live daemon ignores PYTHONPATH `sitecustomize.py` via `-I`.
            py_poison = root / "py_poison"
            py_poison.mkdir()
            py_mark = root / "sitecustomize_ran.txt"
            (py_poison / "sitecustomize.py").write_text(
                f"from pathlib import Path; Path({str(py_mark)!r}).write_text('pwn')\n",
                encoding="utf-8",
            )
            evil_py_bin = root / "evil_py_path"
            evil_py_bin.mkdir()
            (evil_py_bin / "python3").write_text(
                f'#!/bin/sh\necho pwn > "{py_mark}"\nexit 1\n', encoding="utf-8"
            )
            (evil_py_bin / "python3").chmod(0o755)
            evil_sh = root / "evil_bash_env.sh"
            evil_sh.write_text(f'echo pwn > "{py_mark}"\n', encoding="utf-8")
            py_env = _scrubbed_env({
                "ANNEAL_LEAN": str(lean_shim),
                "ANNEAL_LSP_SOCKET": str(root / "py_sock/lsp.sock"),
                "ANNEAL_LSP_NO_SANDBOX": "1",
                "PATH": f"{evil_py_bin}{os.pathsep}{os.environ.get('PATH', '/usr/bin:/bin')}",
                "PYTHONPATH": str(py_poison),
                "BASH_ENV": str(evil_sh),
                "ENV": str(evil_sh),
                "BASH_FUNC_[%%": f'() {{ echo pwn > "{py_mark}"; }}',
            })
            try:
                subprocess.check_output(
                    [entry, "--help"], cwd=str(root), text=True, env=py_env, timeout=20
                )
                self.assertFalse(py_mark.exists())
                out_py = subprocess.check_output(
                    [sys.executable, "-I", "-B", entry, "--json", "diag", "sub/Main.lean"],
                    cwd=str(root), text=True, env=py_env, timeout=20,
                )
                self.assertTrue(json.loads(out_py)["completed"])
                self.assertFalse(py_mark.exists())
            finally:
                subprocess.run(
                    [sys.executable, "-B", entry, "stop-daemon"],
                    env=py_env, check=False, timeout=10,
                )

            # Forward ANNEAL_TEST_INSTALL_ROOT prebuilts via daemon mode.
            inst_root = root / "inst_root"
            (inst_root / "share/anneal/prebuilt/Trusted").mkdir(parents=True)
            (inst_root / "share/anneal/prebuilt/Trusted/MirAst.olean").write_bytes(b"")
            (inst_root / "lean/bin").mkdir(parents=True)
            (inst_root / "lean/bin/lean").symlink_to(lean_shim)
            ann_repo = root / "ann_repo"
            (ann_repo / "anneal/trusted/lean").mkdir(parents=True)
            (ann_repo / "anneal/trusted/lean/Trusted.lean").write_text("", encoding="utf-8")
            (ann_repo / "anneal/theory").mkdir(parents=True)
            (ann_repo / "anneal/theory/Th.lean").write_text("def th := 1\n", encoding="utf-8")
            ir_env = _scrubbed_env({
                "ANNEAL_LEAN": str(lean_shim),
                "ANNEAL_TEST_INSTALL_ROOT": str(inst_root),
                "ANNEAL_LSP_SOCKET": str(root / "ir_sock/lsp.sock"),
                "ANNEAL_LSP_NO_SANDBOX": "1",
            })
            try:
                ir_dir = run_cmd(["--direct", "hover", str(ann_repo / "anneal/theory/Th.lean"),
                                  "1"], ir_env)
                ir_dae = run_cmd(["hover", str(ann_repo / "anneal/theory/Th.lean"), "1"], ir_env)
                self.assertIn(str((inst_root / "share/anneal/prebuilt").resolve()),
                              json.loads(str(ir_dir["hover"]))["lean_path"])
                self.assertIn(str((inst_root / "share/anneal/prebuilt").resolve()),
                              json.loads(str(ir_dae["hover"]))["lean_path"])
            finally:
                subprocess.run(
                    [sys.executable, "-B", entry, "stop-daemon"],
                    cwd=str(root), env=ir_env, check=False, timeout=10,
                )

            # Symlinked $HOME accepts file, --artifacts, and CARGO_TARGET_DIR.
            sym_tgt_h = root / "sym_tgt_home"
            (sym_tgt_h / "ws").mkdir(parents=True)
            (sym_tgt_h / "ws/request.json").write_text("{}", encoding="utf-8")
            (sym_tgt_h / "ws/S.lean").write_text("def s := 1\n", encoding="utf-8")
            (sym_tgt_h / "art/lean-lib").mkdir(parents=True)
            (sym_tgt_h / "art/lean-lib/Expected.olean").write_bytes(b"")
            (sym_tgt_h / "target/anneal-artifacts/ws/lean-lib").mkdir(parents=True)
            (sym_tgt_h / "target/anneal-artifacts/ws/lean-lib/Expected.olean").write_bytes(b"")
            sym_h = root / "sym_link_home"
            sym_h.symlink_to(sym_tgt_h)
            sym_sock = sym_tgt_h / "sym_sock/lsp.sock"
            sym_env_art = _scrubbed_env({
                "HOME": str(sym_h), "ANNEAL_LEAN": str(lean_shim),
                "ANNEAL_LSP_SOCKET": str(sym_sock), "ANNEAL_LSP_NO_SANDBOX": "1",
                "ANNEAL_LSP_ARTIFACTS": f"{sym_h}/art",
            })
            sym_env_ct = _scrubbed_env({
                "HOME": str(sym_h), "ANNEAL_LEAN": str(lean_shim),
                "ANNEAL_LSP_SOCKET": str(sym_sock), "ANNEAL_LSP_NO_SANDBOX": "1",
                "CARGO_TARGET_DIR": f"{sym_h}/target",
            })
            try:
                for env_cur, tag in ((sym_env_art, "art"), (sym_env_ct, "target")):
                    d_sym = run_cmd(["--direct", "hover", f"{sym_h}/ws/S.lean", "1"], env_cur)
                    dae_sym = run_cmd(["hover", f"{sym_h}/ws/S.lean", "1"], env_cur)
                    self.assertIn(tag, json.loads(str(d_sym["hover"]))["lean_path"])
                    self.assertIn(tag, json.loads(str(dae_sym["hover"]))["lean_path"])
            finally:
                subprocess.run(
                    [sys.executable, "-B", entry, "stop-daemon"],
                    cwd=str(root), env=sym_env_art, check=False, timeout=10,
                )

            # Relative ANNEAL_LSP_SOCKET stays isolated from daemon cwd='/'.
            (root / "usr").mkdir(mode=0o700)
            sock_cwd = root / "sock_cwd"
            sock_cwd.mkdir(mode=0o700)
            rel_cases = (
                ("lsp.sock", str(sock_cwd), str(root / "sub/Main.lean")),
                ("relsock/lsp.sock", str(root), "sub/Main.lean"),
                ("usr/lsp.sock", str(root), "sub/Main.lean"),
            )
            for rel_sock, run_cwd, target in rel_cases:
                rel_env = _scrubbed_env({
                    "ANNEAL_LEAN": str(lean_shim),
                    "ANNEAL_LSP_SOCKET": rel_sock,
                    "ANNEAL_LSP_NO_SANDBOX": "1",
                })
                try:
                    rd = json.loads(subprocess.check_output(
                        [sys.executable, "-B", entry, "--json", "diag", target],
                        cwd=run_cwd, text=True, env=rel_env, timeout=20,
                    ))
                    self.assertTrue(rd["completed"])
                    rf = json.loads(subprocess.check_output(
                        [sys.executable, "-B", entry, "--json", "def", target, "1"],
                        cwd=run_cwd, text=True, env=rel_env, timeout=20,
                    ))
                    self.assertIn("theorem x", str(rf["locations"][0]["snippet"]))
                finally:
                    subprocess.run(
                        [sys.executable, "-B", entry, "stop-daemon"],
                        cwd=run_cwd, env=rel_env, check=False, timeout=10,
                    )

            if sys.platform.startswith("linux") and os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.assertTrue(_bwrap_usable(check_python=True))
            if _bwrap_usable(check_python=True):
                # Relative socket in sandbox keeps `/` & `/usr` intact.
                sbx_rel_cases = (
                    ("sbx.sock", str(sock_cwd), str(root / "sub/Main.lean")),
                    ("usr/sbx_lsp.sock", str(root), "sub/Main.lean"),
                )
                for rel_sock, run_cwd, target in sbx_rel_cases:
                    rs_env = _scrubbed_env({
                        "ANNEAL_LEAN": str(lean_shim),
                        "ANNEAL_LSP_SOCKET": rel_sock,
                    })
                    try:
                        rd = json.loads(subprocess.check_output(
                            [sys.executable, "-B", entry, "--json", "diag", target],
                            cwd=run_cwd, text=True, env=rs_env, timeout=20,
                        ))
                        self.assertTrue(rd["completed"] and rd["sandboxed"])
                        rf = json.loads(subprocess.check_output(
                            [sys.executable, "-B", entry, "--json", "def", target, "1"],
                            cwd=run_cwd, text=True, env=rs_env, timeout=20,
                        ))
                        self.assertIn("theorem x", str(rf["locations"][0]["snippet"]))
                    finally:
                        subprocess.run(
                            [sys.executable, "-B", entry, "stop-daemon"],
                            cwd=run_cwd, env=rs_env, check=False, timeout=10,
                        )
                sbx_dir = root / "sub/.anneal_sock"
                sbx_dir.mkdir(mode=0o700)
                sbx_sock = sbx_dir / "lsp.sock"
                sbx_other = sbx_dir / "other.sock"
                ext_sock_dir = root / "ext_svc"
                ext_sock_dir.mkdir()
                ext_sock = ext_sock_dir / "daemon.sock"
                ext_srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                ext_srv.bind(str(ext_sock))
                ext_srv.listen(1)
                sbx_srv = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
                sbx_srv.bind(str(sbx_other))
                sbx_srv.listen(1)
                sbx_env = _scrubbed_env({
                    "ANNEAL_LEAN": str(lean_shim),
                    "ANNEAL_LSP_SOCKET": str(sbx_sock),
                    "LD_LIBRARY_PATH": ".:/opt/lean/lib",
                    "TMPDIR": "/tmp/sbx_secret_tmp",
                })
                try:
                    d1 = run_cmd(["diag", "sub/Main.lean"], sbx_env)
                    d2 = run_cmd(["diag", "sub/Main.lean"], sbx_env)
                    self.assertTrue(d1["sandboxed"] and d1["server_pid"] == d2["server_pid"])
                    probe_cmd, _ = build_sandbox_cmd(
                        [
                            sys.executable, "-c",
                            "import os, socket, sys\n"
                            "for sp in sys.argv[1:]:\n"
                            "    if os.path.exists(sp):\n"
                            "        sys.exit(1)\n"
                            "    try:\n"
                            "        s = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)\n"
                            "        s.connect(sp); s.close(); sys.exit(2)\n"
                            "    except OSError:\n"
                            "        pass\n"
                            "if os.path.exists('/nix/var/nix/daemon-socket'):\n"
                            "    sys.exit(3)\n",
                            str(sbx_sock), str(sbx_other), str(ext_sock),
                        ],
                        ro_binds=[root / "sub"], hidden_paths=[sbx_dir],
                        work_dir=root / "sub", sandbox=True,
                    )
                    self.assertEqual(subprocess.run(probe_cmd, timeout=10).returncode, 0)
                    # Overriding HOME does not expose real /etc/passwd home.
                    sub_res = (root / "sub").resolve()
                    homes_chk = [
                        str(h.resolve()) for h in caller_homes()
                        if h.exists() and not sub_res.is_relative_to(h.resolve())
                    ]
                    if homes_chk:
                        scratch_h = root / "scratch_env_h"
                        scratch_h.mkdir(exist_ok=True)
                        with mock.patch.dict(os.environ, {"HOME": str(scratch_h)}, clear=False):
                            h_probe, _ = build_sandbox_cmd(
                                [
                                    sys.executable, "-c",
                                    "import os, sys\n"
                                    "for rh in sys.argv[1:]:\n"
                                    "    if os.path.exists(rh) and os.listdir(rh):\n"
                                    "        sys.exit(1)\n",
                                    *homes_chk,
                                ],
                                ro_binds=[root / "sub"], work_dir=root / "sub", sandbox=True,
                            )
                        self.assertEqual(subprocess.run(h_probe, timeout=10).returncode, 0)
                    bwrap_anc = root / "bwrap_anc_p"
                    bwrap_ah = bwrap_anc / "home/alice"
                    bwrap_aws = bwrap_ah / "ws"
                    bwrap_aws.mkdir(parents=True)
                    (bwrap_ah / "secret.txt").write_text("SECRET\n", encoding="utf-8")
                    (bwrap_aws / "ok.txt").write_text("OK\n", encoding="utf-8")
                    anc_live, _ = build_sandbox_cmd(
                        [
                            sys.executable, "-c",
                            "import os, sys; sys.exit(0 if os.path.exists('ok.txt') "
                            "and not os.path.exists(sys.argv[1]) else 1)",
                            str((bwrap_ah / "secret.txt").resolve()),
                        ],
                        ro_binds=[bwrap_anc, bwrap_aws], hidden_homes=[bwrap_ah],
                        work_dir=bwrap_aws, sandbox=True,
                    )
                    self.assertEqual(subprocess.run(anc_live, timeout=10).returncode, 0)
                    bwrap_eh = root / "bwrap_elan_h"
                    bwrap_ed = bwrap_eh / ".elan"
                    (bwrap_ed / "bin").mkdir(parents=True)
                    (bwrap_ed / "toolchains/t1/lib/lean").mkdir(parents=True)
                    (bwrap_ed / "settings.toml").write_text("default_toolchain = 't1'\n", "utf-8")
                    (bwrap_eh / "secret.txt").write_text("SECRET\n", "utf-8")
                    (bwrap_ed / "bin/elan").write_text("#!/bin/sh\n", "utf-8")
                    os.link(bwrap_ed / "bin/elan", bwrap_ed / "bin/lean")
                    with mock.patch.dict(os.environ, {"HOME": str(bwrap_eh)}, clear=False):
                        elan_ro = _ro_tc(bwrap_ed / "bin/lean")
                    elan_live, _ = build_sandbox_cmd(
                        [
                            sys.executable, "-c",
                            "import os, sys; sys.exit(0 if "
                            "os.path.isfile(sys.argv[1]) and os.path.isdir(sys.argv[2]) "
                            "and os.path.isfile(sys.argv[3]) and not os.path.exists(sys.argv[4]) "
                            "else 1)",
                            str((bwrap_ed / "settings.toml").resolve()),
                            str((bwrap_ed / "toolchains/t1/lib/lean").resolve()),
                            str((bwrap_ed / "bin/lean").resolve()),
                            str((bwrap_eh / "secret.txt").resolve()),
                        ],
                        ro_binds=[*elan_ro, bwrap_aws], hidden_homes=[bwrap_eh],
                        work_dir=bwrap_aws, sandbox=True,
                    )
                    self.assertEqual(subprocess.run(elan_live, timeout=10).returncode, 0)
                    sbx_srv.close()
                    ext_srv.close()
                    sbx_other.unlink()
                    ext_sock.unlink()
                    bwrap_exe = shutil.which("bwrap") or "/usr/bin/bwrap"
                    uns_probe = subprocess.run(
                        [
                            bwrap_exe, "--ro-bind", "/", "/", "--dev", "/dev",
                            "--proc", "/proc", "--unshare-user", "--", sys.executable, "-I",
                            "-B", "-c",
                            "import sys; sys.path.insert(0, sys.argv[1]); "
                            "from anneal_lsp.client import build_sandbox_cmd; "
                            "c, ok = build_sandbox_cmd(['/bin/true'], sandbox=True); "
                            "assert ok and 'bwrap' in c[0]",
                            str(_CI_DIR),
                        ],
                        capture_output=True, text=True, timeout=10,
                    )
                    self.assertEqual(uns_probe.returncode, 0, uns_probe.stderr)
                    cap_probe_cmd, _ = build_sandbox_cmd(
                        [
                            sys.executable, "-c",
                            "import sys; s = open('/proc/self/status', encoding='utf-8').read();"
                            " sys.exit(0 if 'CapEff:\\t0000000000000000\\n' in s else 1)",
                        ],
                        ro_binds=[root / "sub"], work_dir=root / "sub", sandbox=True,
                    )
                    self.assertEqual(subprocess.run(cap_probe_cmd, timeout=10).returncode, 0)
                    can_uns = subprocess.run(
                        ["unshare", "-r", "/bin/true"], capture_output=True, timeout=5,
                    )
                    if can_uns.returncode == 0:
                        um_cmd, _ = build_sandbox_cmd(
                            ["/bin/sh", "-c", "umount /tmp >/dev/null 2>&1 && exit 1 || exit 0"],
                            ro_binds=[root / "sub"], work_dir=root / "sub", sandbox=True,
                        )
                        um_res = subprocess.run(["unshare", "-r", *um_cmd], timeout=10)
                        self.assertEqual(um_res.returncode, 0)
                    hv_sbx = json.loads(
                        str(run_cmd(["hover", "sub/Main.lean", "1"], sbx_env)["hover"])
                    )
                    self.assertEqual((hv_sbx["ld"], hv_sbx["tmpdir"]), ("", ""))
                    hv_dir = json.loads(
                        str(run_cmd(["--direct", "hover", "sub/Main.lean", "1"], sbx_env)["hover"])
                    )
                    self.assertEqual((hv_dir["ld"], hv_dir["tmpdir"]), ("/opt/lean/lib", ""))
                    hv_nosbx = json.loads(
                        str(
                            run_cmd(
                                ["--direct", "--no-sandbox", "hover", "sub/Main.lean", "1"],
                                sbx_env,
                            )["hover"]
                        )
                    )
                    self.assertEqual(
                        (hv_nosbx["ld"], hv_nosbx["tmpdir"]),
                        ("/opt/lean/lib", "/tmp/sbx_secret_tmp"),
                    )
                    bad_r = subprocess.run(
                        [sys.executable, "-B", entry, "--no-sandbox", "diag", "sub/Main.lean"],
                        cwd=str(root), env=sbx_env, text=True, capture_output=True, timeout=15,
                    )
                    self.assertNotEqual(bad_r.returncode, 0)
                    # Warmth survives caller thread exit + `--die-with-parent`.
                    with mock.patch.dict(os.environ, sbx_env, clear=True):
                        th_pool = WorkspacePool(sandbox=True, hidden_paths=[sbx_dir])
                        try:
                            with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
                                r1 = ex.submit(
                                    th_pool.diagnostics, str(root / "sub/Main.lean")
                                ).result(timeout=20)
                            with concurrent.futures.ThreadPoolExecutor(max_workers=1) as ex:
                                r2 = ex.submit(
                                    th_pool.diagnostics, str(root / "sub/Main.lean")
                                ).result(timeout=20)
                            self.assertTrue(r1["sandboxed"])
                            self.assertEqual(r1["server_pid"], r2["server_pid"])
                        finally:
                            th_pool.shutdown()
                    if hasattr(socket, "SO_PEERCRED"):
                        sbx_pid = int(d1["server_pid"])
                        with socket.socket(socket.AF_UNIX, socket.SOCK_STREAM) as ps:
                            ps.connect(str(sbx_sock))
                            daemon_pid = struct.unpack(
                                "3i", ps.getsockopt(socket.SOL_SOCKET, socket.SO_PEERCRED, 12)
                            )[0]
                        os.kill(daemon_pid, signal.SIGKILL)
                        for _ in range(40):
                            try:
                                os.kill(sbx_pid, 0)
                            except ProcessLookupError:
                                break
                            time.sleep(0.05)
                        with self.assertRaises(ProcessLookupError):
                            os.kill(sbx_pid, 0)
                finally:
                    ext_srv.close()
                    sbx_srv.close()
                    subprocess.run(
                        [sys.executable, "-B", entry, "stop-daemon"],
                        env=sbx_env, check=False, timeout=10,
                    )


class LiveLeanServerIntegrationTest(unittest.TestCase):
    def test_live_lean_server_warmth_tools_and_multi_attempt(self) -> None:
        lean_bin = _maybe_live_lean()
        if lean_bin is None:
            msg = "no Lean 4 toolchain installed"
            if os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.fail(msg)
            self.skipTest(msg)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            unit = root / "unit"
            unit.mkdir()
            (unit / "request.json").write_text("{}", encoding="utf-8")
            art = root / "art"
            (art / "lean-lib").mkdir(parents=True)
            spec = unit / "Spec.lean"
            spec.write_text("def targetVal : Nat := 42\n", encoding="utf-8")
            subprocess.check_call(
                [str(lean_bin), "-R", str(unit), "-o", str(art / "lean-lib/Spec.olean"), str(spec)],
                cwd=str(unit), timeout=30,
            )
            lean_file = unit / "Sample.lean"
            lines = [
                "import Spec",
                "theorem add_zero_demo (n : Nat) : n + 0 = n ∧ targetVal = 42 := by",
                "  sorry -- main_tgt",
                "theorem multi_sorry : 1 = 1 ∧ 2 = 2 := by",
                "  constructor",
                "  · sorry -- first_sorry",
                "  · sorry",
                "theorem inline_pair : 1 = 1 ∧ 2 = 2 := by",
                "  exact ⟨by sorry, by sorry⟩ -- pair_tgt",
                "theorem prior_err_decl : 1 = 1 := by",
                "  bogus_prior",
                "  sorry -- prior_tgt",
                "theorem term_demo : 1 = 1 := sorry -- term_tgt",
                "namespace NS",
                "protected theorem prot_ok : 1 = 1 := by",
                "  sorry -- prot_tgt",
                "end NS",
                "theorem have_inline : 1 = 1 := by",
                "  have h : 2 = 2 := by sorry",
                "  exact rfl",
                "def astral_demo : Nat := by",
                '  let _ := "\U00010348"; exact targetVal -- astral_line',
                "def «sorry» : Nat := 1",
                "def «admit» : Nat := 2",
                "theorem root_sorryax_demo : False := «_root_».sorryAx _ false -- rsax_tgt",
                'def neg_str_demo : Bool := !"{".isEmpty',
                "theorem after_neg_demo : 1 = 1 := by",
                "  sorry -- after_neg_tgt",
                'def lit_sorry_demo : String := "sorry"',
            ]
            body = "\n".join(lines) + "\n"
            lean_file.write_text(body, encoding="utf-8")
            ln = lambda pat: next(i for i, txt in enumerate(lines, 1) if pat in txt)

            if sys.platform.startswith("linux") and os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.assertTrue(_bwrap_usable())
            use_sbx = _bwrap_usable()
            live_env = _scrubbed_env({"ANNEAL_LEAN": str(lean_bin)})
            with mock.patch.dict(os.environ, live_env, clear=True):
                pool = WorkspacePool(sandbox=use_sbx)
                try:
                    d1 = pool.diagnostics(str(lean_file), artifacts_dir=art)
                    d2 = pool.diagnostics(str(lean_file), artifacts_dir=art)
                    self.assertEqual(d1["server_pid"], d2["server_pid"])
                    self.assertEqual(d1["sandboxed"], use_sbx)
                    self.assertTrue(d1["completed"])
                    s_goals = [g for g in d1["sorry_goals"] if g["line"] == ln("main_tgt")][0]
                    self.assertIn("targetVal = 42", s_goals["goals"][0])
                    p_goals = [g for g in d1["sorry_goals"] if g["line"] == ln("pair_tgt")]
                    self.assertEqual(len(p_goals), 2)
                    self.assertIn("1 = 1", p_goals[0]["goals"][0])
                    self.assertIn("2 = 2", p_goals[1]["goals"][0])
                    self.assertEqual(d1["sorry_count"], 11)
                    self.assertIn(ln("rsax_tgt"), d1["sorry_lines"])
                    self.assertIn(ln("after_neg_tgt"), d1["sorry_lines"])
                    self.assertIn("targetVal = 42", d1["text"])
                    mcp_d = handle_mcp_request(pool, {
                        "jsonrpc": "2.0", "id": 88, "method": "tools/call",
                        "params": {
                            "name": "lean_diagnostics",
                            "arguments": {"file": str(lean_file), "artifacts_dir": str(art)},
                        },
                    })
                    assert mcp_d is not None
                    self.assertIn("targetVal = 42", mcp_d["result"]["content"][0]["text"])

                    g = pool.goal(str(lean_file), ln("main_tgt"), artifacts_dir=art)
                    self.assertIn("targetVal = 42", "\n".join(g["goals_before"]))
                    ga = pool.goal(
                        str(lean_file), ln("astral_line"),
                        snippet="exact targetVal", artifacts_dir=art,
                    )
                    self.assertIn("Nat", "\n".join(ga["goals_focus"]))

                    ma = pool.multi_attempt(
                        str(lean_file), ln("main_tgt"),
                        ["sorry", "rfl", "constructor", "exact ⟨Nat.add_zero n, rfl⟩"],
                        artifacts_dir=art,
                    )["attempts"]
                    self.assertTrue(ma[0]["uses_sorry"] and not ma[0]["closes_goal"])
                    self.assertFalse(ma[1]["closes_goal"])
                    self.assertTrue(ma[2]["ok_step"] and not ma[2]["closes_goal"])
                    self.assertTrue(ma[3]["closes_goal"])
                    rsax_att = pool.multi_attempt(
                        str(lean_file), ln("after_neg_tgt"),
                        ["exact «_root_».sorryAx _ false"], artifacts_dir=art,
                    )["attempts"][0]
                    self.assertTrue(rsax_att["uses_sorry"] and not rsax_att["closes_goal"])

                    pe = pool.multi_attempt(
                        str(lean_file), ln("prior_tgt"), ["rfl"], artifacts_dir=art
                    )["attempts"][0]
                    self.assertFalse(pe["evaluated"])
                    for tag in ("term_tgt", "prot_tgt", "have h :"):
                        att = pool.multi_attempt(
                            str(lean_file), ln(tag), ["rfl"], artifacts_dir=art
                        )["attempts"][0]
                        self.assertTrue(att["closes_goal"], (tag, att))
                    for tag in ("first_sorry", "pair_tgt"):
                        inc_res = pool.multi_attempt(
                            str(lean_file), ln(tag), ["rfl"], artifacts_dir=art
                        )
                        inc_att = inc_res["attempts"][0]
                        self.assertTrue(inc_att["uses_sorry"] and not inc_att["closes_goal"], tag)
                        self.assertIn("INCOMPLETE", inc_res["text"])

                    hv_live = pool.hover(
                        str(lean_file), ln("astral_line"), symbol="targetVal", artifacts_dir=art
                    )
                    self.assertIn("Nat", hv_live["hover"])
                    df = pool.definition(
                        str(lean_file), ln("main_tgt") - 1, symbol="targetVal", artifacts_dir=art
                    )
                    self.assertTrue(any("Spec.lean" in loc["file"] for loc in df["locations"]))
                    comp = pool.completions(str(lean_file), ln("main_tgt"), artifacts_dir=art)
                    self.assertIsInstance(comp["items"], list)
                    outl = pool.outline(str(lean_file), artifacts_dir=art)
                    self.assertTrue(any(s["name"] == "add_zero_demo" for s in outl["symbols"]))
                    sr_live = pool.local_search("add_zero", workspace=str(unit))
                    self.assertTrue(any(m["name"] == "add_zero_demo" for m in sr_live["matches"]))

                    crash_eval = unit / "CrashEval.lean"
                    crash_body = (
                        "unsafe def bad : String := unsafeCast (1 : Nat)\n"
                        "#eval bad.length\n"
                        "theorem crash_after : 1 = 1 := by\n  sorry\n"
                        if sys.platform == "win32"
                        else "#eval show IO Unit from do\n"
                        '  let _ ← IO.Process.output '
                        '{ cmd := "/bin/sh", args := #["-c", "kill -9 $PPID"] }\n'
                        "theorem crash_after : 1 = 1 := by\n  sorry\n"
                    )
                    crash_eval.write_text(crash_body, encoding="utf-8")
                    live_cr = pool.diagnostics(str(crash_eval))
                    self.assertFalse(live_cr["completed"] or live_cr["timed_out"], live_cr)
                    self.assertGreaterEqual(live_cr["error_count"], 1, live_cr)
                    self.assertEqual(live_cr["sorry_goals"], [], live_cr)
                    live_g_cr = pool.goal(str(crash_eval), 3)
                    self.assertFalse(live_g_cr["completed"] or live_g_cr["timed_out"], live_g_cr)
                    self.assertLess(live_g_cr["elapsed_ms"], 2000.0)
                    live_h_cr = pool.hover(str(crash_eval), 3)
                    self.assertFalse(live_h_cr["completed"] or live_h_cr["timed_out"], live_h_cr)
                    live_ma_cr = pool.multi_attempt(str(crash_eval), 4, ["rfl"])
                    self.assertFalse(live_ma_cr["attempts"][0]["evaluated"], live_ma_cr)
                    crash_eval.write_text(
                        "theorem crash_after : 1 = 1 := by\n  rfl\n", encoding="utf-8"
                    )
                    live_rec = pool.diagnostics(str(crash_eval))
                    self.assertTrue(live_rec["completed"] and not live_rec["timed_out"], live_rec)
                    self.assertEqual(live_rec["error_count"], 0, live_rec)

                    if _bwrap_usable():
                        d_env = _scrubbed_env({
                            "ANNEAL_LEAN": str(lean_bin),
                            "ANNEAL_LSP_SOCKET": str(root / "live_d/lsp.sock"),
                            "ANNEAL_LSP_ARTIFACTS": str(art),
                        })
                        try:
                            out = subprocess.check_output(
                                [sys.executable, "-B", str(_CI_DIR / "anneal-lsp"), "--json", "try",
                                 str(lean_file), str(ln("term_tgt")), "rfl"],
                                cwd=str(unit), text=True, env=d_env, timeout=30,
                            )
                            self.assertTrue(json.loads(out)["attempts"][0]["closes_goal"])
                        finally:
                            subprocess.run(
                                [sys.executable, "-B", str(_CI_DIR / "anneal-lsp"), "stop-daemon"],
                                cwd=str(unit), env=d_env, capture_output=True, timeout=10,
                            )
                    self.assertEqual(lean_file.read_text(encoding="utf-8"), body)
                    self.assertFalse((unit / ".lake").exists())
                finally:
                    pool.shutdown()

                if (lean_bin.parent / "lake").is_file():
                    lk = root / "lake_demo"
                    lk.mkdir()
                    (lk / "lakefile.toml").write_text(
                        'name = "demo"\ndefaultTargets = ["Demo"]\n'
                        '[[lean_lib]]\nname = "Demo"\n',
                        encoding="utf-8",
                    )
                    (lk / "Demo.lean").write_text(
                        "theorem lake_ok : 1 = 1 := by\n  sorry\n", "utf-8"
                    )
                    lk_pool = WorkspacePool(sandbox=False)
                    try:
                        self.assertEqual(lk_pool.diagnostics(str(lk / "Demo.lean"))["mode"], "lake")
                        lk_att = lk_pool.multi_attempt(
                            str(lk / "Demo.lean"), 2, ["rfl"]
                        )["attempts"][0]
                        self.assertTrue(lk_att["closes_goal"])
                    finally:
                        lk_pool.shutdown()


if __name__ == "__main__":
    unittest.main()
