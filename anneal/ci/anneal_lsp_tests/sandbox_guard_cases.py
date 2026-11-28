# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lsp` tests for the sandbox, the daemon socket, and hung-close
guards."""

from __future__ import annotations

from .support import (
    Any,
    build_sandbox_cmd,
    _check_daemon_ping,
    _CI_DIR,
    cli_main,
    discover_workspace,
    io,
    _is_trusted_bwrap_path,
    LspProcess,
    mock,
    os,
    Path,
    PINNED_TOOLCHAIN,
    _ro_tc,
    shutil,
    signal,
    socket,
    stat,
    subprocess,
    sys,
    tempfile,
    threading,
    time,
    types,
    unittest,
    warnings,
    WorkspaceWorker,
)

# The strict-mode check in `test_sandbox_socket_and_hung_close_guards` runs
# the live-server case directly, with `_maybe_live_lean` patched in the module
# that case reads it from.
from . import live_server_cases


class LiveLeanServerIntegrationTest(
    live_server_cases.LiveServerCases, unittest.TestCase
):
    """The live-server case as a `TestCase` for that check to instantiate.

    `test_anneal_lsp` composes the class that `unittest` discovers.
    """


class SandboxGuardCases:
    """`DiscoveryAndProtocolTests` methods for the sandbox, the socket, and
    hung-close guards."""

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
            with mock.patch.object(live_server_cases, "_maybe_live_lean", return_value=None):
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
