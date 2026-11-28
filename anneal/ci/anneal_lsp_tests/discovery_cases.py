# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`anneal-lsp` tests for UTF-16 positions, declaration matching, and workspace
and toolchain discovery."""

from __future__ import annotations

from .support import (
    Any,
    _bwrap_usable,
    caller_homes,
    _CI_DIR,
    cli_main,
    discover_workspace,
    find_lean_binary,
    find_lean_binary_optional,
    hashlib,
    io,
    json,
    mask_lean_comments,
    _match_decl,
    mock,
    os,
    Path,
    py_col_to_utf16,
    _scrubbed_env,
    tempfile,
    time,
    uri_to_path,
    utf16_to_py_col,
)


class DiscoveryCases:
    """`DiscoveryAndProtocolTests` methods for positions, declaration
    matching, and discovery."""

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
