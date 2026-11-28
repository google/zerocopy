# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lsp` tests for the mock Lean server, multi-attempt, hover, restarts,
and admissions."""

from __future__ import annotations

from .support import (
    discover_workspace,
    handle_mcp_request,
    json,
    mock,
    _MOCK_LSP_SERVER,
    os,
    Path,
    _scrubbed_env,
    sys,
    tempfile,
    time,
    WorkspacePool,
)


class MockPoolCases:
    """`MockLspAndMcpTests` methods for the mock Lean server and the first
    pool checks."""

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
                    self._check_attempts_hover_eviction_and_severity(root, unit, proof, pool, orig_body, orig_mtime)
                    ext_secret, multi_doc = self._check_restarts_admissions_and_timeouts(root, unit, proof, pool)
                    self._check_restart_and_diagnostic_recovery(unit, proof, pool)
                    self._check_child_failures_and_worker_limits(root, unit, pool)
                    self._check_symlinks_protocol_and_cli_options(root, unit, proof, pool, lean_shim, ext_secret, multi_doc)
                finally:
                    pool.shutdown()

    def _check_attempts_hover_eviction_and_severity(
        self,
        root: Path,
        unit: Path,
        proof: Path,
        pool: WorkspacePool,
        orig_body: str,
        orig_mtime: int,
    ) -> None:
        """Check multi-attempt results, hover, eviction outside the pool
        lock, FIFO sources, and severity filtering.

        One stage of `test_multi_attempt_hover_lock_free_evict_and_mcp`,
        run inside its mock environment with its worker pool.
        """
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

    def _check_restarts_admissions_and_timeouts(
        self,
        root: Path,
        unit: Path,
        proof: Path,
        pool: WorkspacePool,
    ) -> tuple[Path, Path]:
        """Check artifact-driven restarts, Lake binaries, untrusted
        definitions, remaining admissions, and query timeouts.

        One stage of `test_multi_attempt_hover_lock_free_evict_and_mcp`,
        run inside its mock environment with its worker pool.
        """
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

        return ext_secret, multi_doc
