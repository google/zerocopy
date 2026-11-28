# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lsp` tests for worker restarts, diagnostic recovery, child failures,
and worker limits."""

from __future__ import annotations

from .support import (
    Any,
    concurrent,
    LspProcess,
    LspRpcError,
    mock,
    os,
    Path,
    _scrubbed_env,
    sys,
    threading,
    time,
    WorkspacePool,
)


class MockRecoveryCases:
    """`MockLspAndMcpTests` checks for worker recovery and limits."""

    def _check_restart_and_diagnostic_recovery(
        self,
        unit: Path,
        proof: Path,
        pool: WorkspacePool,
    ) -> None:
        """Check sibling-edit restarts, malformed frames, and diagnostic
        waits, retries, and recovery.

        One stage of `test_multi_attempt_hover_lock_free_evict_and_mcp`,
        run inside its mock environment with its worker pool.
        """
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

    def _check_child_failures_and_worker_limits(
        self,
        root: Path,
        unit: Path,
        pool: WorkspacePool,
    ) -> None:
        """Check child failures, sorry-line preservation, and
        `max_workers` and LRU eviction.

        One stage of `test_multi_attempt_hover_lock_free_evict_and_mcp`,
        run inside its mock environment with its worker pool.
        """
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
