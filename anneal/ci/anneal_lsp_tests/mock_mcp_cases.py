# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lsp` tests for MCP protocol and CLI options and the daemon."""

from __future__ import annotations

from .support import (
    build_sandbox_cmd,
    _bwrap_usable,
    caller_homes,
    _CI_DIR,
    cli_main,
    concurrent,
    default_socket_path,
    handle_mcp_request,
    io,
    json,
    mock,
    os,
    Path,
    _ro_tc,
    _scrubbed_env,
    serve_mcp,
    shutil,
    signal,
    socket,
    struct,
    subprocess,
    sys,
    tempfile,
    time,
    WorkspacePool,
)


class MockMcpCases:
    """`MockLspAndMcpTests` methods for MCP options and the daemon."""

    def _check_symlinks_protocol_and_cli_options(
        self,
        root: Path,
        unit: Path,
        proof: Path,
        pool: WorkspacePool,
        lean_shim: Path,
        ext_secret: Path,
        multi_doc: Path,
    ) -> None:
        """Check symlinked targets, positions, protocol negotiation, MCP
        CLI options and schemas, and artifact-directory precedence.

        One stage of `test_multi_attempt_hover_lock_free_evict_and_mcp`,
        run inside its mock environment with its worker pool.
        """
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
