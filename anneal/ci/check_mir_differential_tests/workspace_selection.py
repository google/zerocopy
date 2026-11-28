# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Cargo workspace member selection and `mir-eval` flag tests for
`check_mir_differential.py`."""

from __future__ import annotations

import json
import os
from pathlib import Path
import tempfile
from typing import Any
from unittest import mock

import check_mir_differential as cmd
from check_mir_differential_tests.support import _sample_diff_report


class WorkspaceSelectionCases:
    def test_nonvirtual_workspace_default_members_selection(self) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            root_manifest = root / "Cargo.toml"
            member_dir = root / "tools" / "anneal-mir-eval"
            member_dir.mkdir(parents=True)
            member_manifest = member_dir / "Cargo.toml"
            member_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            other_dir = root / "tools" / "other-eval"
            other_dir.mkdir(parents=True)
            other_manifest = other_dir / "Cargo.toml"
            other_manifest.write_text(
                '[package]\nname = "other-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            excl_dir = root / "tools" / "excluded-eval"
            excl_dir.mkdir(parents=True)
            excl_manifest = excl_dir / "Cargo.toml"
            excl_manifest.write_text(
                '[package]\nname = "excl-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            target_bin = root / "target" / "debug" / "anneal-mir-eval"
            target_bin.parent.mkdir(parents=True)
            target_bin.write_text("", encoding="utf-8")

            def _artifact(manifest: Path) -> str:
                return json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(manifest),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(target_bin),
                    }
                )

            # Package + workspace with explicit `default-members` permits the
            # selected default member while excluding unselected members,
            # excluded dirs, and `"."` when omitted from `default-members`.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n'
                'exclude = ["tools/excluded-eval"]\n'
                'default-members = ["tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(other_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(excl_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                )
            )

            # Including `"."` alongside a member in `default-members` permits
            # both root and selected member manifests.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n'
                'default-members = [".", "tools/anneal-mir-eval"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )

            # Package + workspace without `default-members` targets only root.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\n',
                encoding="utf-8",
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                ),
                target_bin,
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                )
            )

            # Explicit empty `default-members` rejects all manifests.
            root_manifest.write_text(
                '[package]\nname = "root"\nversion = "0.1.0"\n'
                '[workspace]\nmembers = ["tools/*"]\ndefault-members = []\n',
                encoding="utf-8",
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(root_manifest), "anneal-mir-eval", root_manifest
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    _artifact(member_manifest), "anneal-mir-eval", root_manifest
                )
            )

    def test_virtual_workspace_manifest_and_mutually_exclusive_mir_eval_flags(
        self,
    ) -> None:
        with tempfile.TemporaryDirectory() as tmpd:
            root = Path(tmpd).resolve()
            anneal_dir = root / "anneal"
            anneal_dir.mkdir()

            vws_manifest = root / "Cargo.toml"
            vws_manifest.write_text(
                '[workspace]\nresolver = "2"\nmembers = ["tools/*"]\n'
                'exclude = ["tools/excluded-eval"]\n',
                encoding="utf-8",
            )
            member_dir = root / "tools" / "anneal-mir-eval"
            member_dir.mkdir(parents=True)
            member_manifest = member_dir / "Cargo.toml"
            member_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            excl_dir = root / "tools" / "excluded-eval"
            excl_dir.mkdir(parents=True)
            excl_manifest = excl_dir / "Cargo.toml"
            excl_manifest.write_text(
                '[package]\nname = "anneal-mir-eval"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            target_bin = root / "target" / "debug" / "anneal-mir-eval"
            target_bin.parent.mkdir(parents=True)
            target_bin.write_text("", encoding="utf-8")

            member_artifact = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "manifest_path": str(member_manifest),
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(target_bin),
                }
            )
            self.assertEqual(
                cmd._extract_built_executable(
                    member_artifact, "anneal-mir-eval", vws_manifest
                ),
                target_bin,
            )

            # Excluded workspace dirs and conflicting duplicate artifacts fail
            # closed.
            excluded_artifact = json.dumps(
                {
                    "reason": "compiler-artifact",
                    "manifest_path": str(excl_manifest),
                    "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                    "profile": {"test": False},
                    "executable": str(target_bin),
                }
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    excluded_artifact, "anneal-mir-eval", vws_manifest
                )
            )
            other_member_dir = root / "tools" / "other-eval"
            other_member_dir.mkdir(parents=True)
            other_manifest = other_member_dir / "Cargo.toml"
            other_manifest.write_text(
                '[package]\nname = "other"\nversion = "0.1.0"\n',
                encoding="utf-8",
            )
            dup_stdout = (
                member_artifact
                + "\n"
                + json.dumps(
                    {
                        "reason": "compiler-artifact",
                        "manifest_path": str(other_manifest),
                        "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                        "profile": {"test": False},
                        "executable": str(root / "target" / "debug" / "other"),
                    }
                )
            )
            self.assertIsNone(
                cmd._extract_built_executable(
                    dup_stdout, "anneal-mir-eval", vws_manifest
                )
            )

            # End-to-end `maybe_run_mir_eval_manifest` accepts a virtual
            # workspace manifest whose `compiler-artifact` identifies the
            # member `Cargo.toml`.
            def _vws_cargo_side_effect(
                args: list[str], **_kwargs: Any
            ) -> mock.Mock:
                if "build" in args:
                    return mock.Mock(
                        returncode=0,
                        stdout=member_artifact + "\n",
                        stderr="",
                    )
                return mock.Mock(returncode=0, stdout="", stderr="")

            with mock.patch(
                "subprocess.run", side_effect=_vws_cargo_side_effect
            ):
                status_vws, bin_vws = cmd.maybe_run_mir_eval_manifest(
                    vws_manifest
                )
            self.assertTrue(status_vws["passed"], status_vws)
            self.assertEqual(bin_vws, target_bin)

            # Passing both `--mir-eval-manifest` and `--mir-eval-bin` is
            # rejected before running any child process.
            with (
                mock.patch.object(
                    cmd, "maybe_run_mir_eval_manifest"
                ) as run_manifest_mock,
                mock.patch.object(cmd, "run_anneal_diff") as run_diff_mock,
            ):
                with self.assertRaises(SystemExit) as ctx:
                    cmd.main(
                        [
                            "--anneal-root",
                            str(anneal_dir),
                            "--mir-eval-manifest",
                            str(member_manifest),
                            "--mir-eval-bin",
                            str(target_bin),
                            "--allow-unknown-git",
                        ]
                    )
                self.assertEqual(ctx.exception.code, 2)
                run_manifest_mock.assert_not_called()
                run_diff_mock.assert_not_called()

            # `maybe_run_mir_eval_manifest` anchors relative Cargo tool and
            # home/target environment overrides against `caller_cwd` before
            # invoking Cargo with `cwd=manifest_canon.parent`.
            caller_root = root / "caller-launch-dir"
            caller_root.mkdir()
            recorded_manifest_envs: list[tuple[list[str], Path, dict[str, str]]] = []

            def _anchored_cargo_side_effect(
                args: list[str],
                *,
                cwd: Path | None = None,
                env: dict[str, str] | None = None,
                **_kwargs: object,
            ) -> mock.Mock:
                recorded_manifest_envs.append(
                    (list(args), Path(cwd) if cwd else Path.cwd(), dict(env or {}))
                )
                if len(args) >= 2 and args[1] == "build":
                    return mock.Mock(
                        returncode=0,
                        stdout=json.dumps(
                            {
                                "reason": "compiler-artifact",
                                "manifest_path": str(member_manifest.resolve()),
                                "target": {"kind": ["bin"], "name": "anneal-mir-eval"},
                                "profile": {"test": False},
                                "executable": str(target_bin),
                            }
                        )
                        + "\n",
                        stderr="",
                    )
                return mock.Mock(returncode=0, stdout="", stderr="")

            prev_cwd = Path.cwd()
            try:
                os.chdir(caller_root)
                with (
                    mock.patch.dict(
                        os.environ,
                        {
                            "CARGO": "./scripts/cargo-wrap",
                            "RUSTC": "./scripts/rustc-wrap",
                            "RUSTDOC": "./scripts/rustdoc-wrap",
                            "RUSTC_WRAPPER": "./scripts/clippy-wrap",
                            "RUSTC_WORKSPACE_WRAPPER": "sccache",
                            "CARGO_HOME": "./rel-cargo-home",
                            "CARGO_TARGET_DIR": "./rel-cargo-target",
                            "PATH": f"./toolchain/bin{os.pathsep}/usr/bin",
                            "LD_LIBRARY_PATH": f"./lib{os.pathsep}/usr/lib",
                        },
                        clear=False,
                    ),
                    mock.patch(
                        "subprocess.run", side_effect=_anchored_cargo_side_effect
                    ),
                ):
                    rel_manifest = Path(os.path.relpath(member_manifest, caller_root))
                    st_anchor, bin_anchor = cmd.maybe_run_mir_eval_manifest(rel_manifest)
            finally:
                os.chdir(prev_cwd)

            self.assertTrue(st_anchor["passed"], st_anchor)
            self.assertEqual(bin_anchor, target_bin)
            self.assertEqual(len(recorded_manifest_envs), 2)
            for call_args, call_cwd, call_env in recorded_manifest_envs:
                self.assertEqual(call_cwd, member_manifest.resolve().parent)
                self.assertEqual(
                    call_args[0], str(caller_root / "scripts" / "cargo-wrap")
                )
                self.assertEqual(
                    call_env["RUSTC"], str(caller_root / "scripts" / "rustc-wrap")
                )
                self.assertEqual(
                    call_env["RUSTDOC"], str(caller_root / "scripts" / "rustdoc-wrap")
                )
                self.assertEqual(
                    call_env["RUSTC_WRAPPER"],
                    str(caller_root / "scripts" / "clippy-wrap"),
                )
                self.assertEqual(call_env["RUSTC_WORKSPACE_WRAPPER"], "sccache")
                self.assertEqual(
                    call_env["CARGO_HOME"], str(caller_root / "rel-cargo-home")
                )
                self.assertEqual(
                    call_env["CARGO_TARGET_DIR"],
                    str(caller_root / "rel-cargo-target"),
                )
                self.assertEqual(
                    call_env["PATH"],
                    f"{caller_root / 'toolchain' / 'bin'}{os.pathsep}/usr/bin",
                )
                self.assertEqual(
                    call_env["LD_LIBRARY_PATH"],
                    f"{caller_root / 'lib'}{os.pathsep}/usr/lib",
                )

            # Explicit `--commit-sha` / `--commit-unix-ts` / `--branch`
            # populate telemetry without `--allow-unknown-git` even outside git.
            out_rev = root / "rev-detail.json"
            perf_rev = root / "rev-perf-record.json"
            explicit_sha = "A" * 40
            with mock.patch.object(
                cmd, "run_anneal_diff", return_value=(0, _sample_diff_report())
            ):
                rc_rev = cmd.main(
                    [
                        "--anneal-root",
                        str(anneal_dir),
                        "--branch",
                        "ci-main",
                        "--commit-sha",
                        explicit_sha,
                        "--commit-unix-ts",
                        "1785000123",
                        "--output",
                        str(out_rev),
                        "--perf-record-out",
                        str(perf_rev),
                    ]
                )
            self.assertEqual(rc_rev, 0)
            detail_rev = json.loads(out_rev.read_text(encoding="utf-8"))
            self.assertEqual(detail_rev["branch"], "ci-main")
            self.assertEqual(detail_rev["commit_sha"], "a" * 40)
            self.assertEqual(detail_rev["commit_unix_ts"], 1785000123)
            rec_rev = json.loads(perf_rev.read_text(encoding="utf-8"))
            self.assertEqual(rec_rev["commit"]["sha"], "a" * 40)
            self.assertEqual(rec_rev["commit"]["unix_ts"], 1785000123)
            self.assertEqual(rec_rev["commit"]["branch"], "ci-main")

            # Invalid or unpaired `--commit-sha` / `--commit-unix-ts` fails
            # closed.
            for bad_flags in (
                ["--commit-sha", "not-a-sha"],
                ["--commit-unix-ts", "-1"],
                ["--commit-sha", "a" * 40],
                ["--commit-unix-ts", "1785000123"],
            ):
                with self.assertRaises(SystemExit) as bad_ctx:
                    cmd.main(
                        ["--anneal-root", str(anneal_dir), *bad_flags]
                    )
                self.assertEqual(bad_ctx.exception.code, 2)
            with self.assertRaisesRegex(ValueError, "provided together"):
                cmd._git_metadata(anneal_dir, commit_sha_override="a" * 40)
            with self.assertRaisesRegex(ValueError, "provided together"):
                cmd._git_metadata(anneal_dir, commit_unix_ts_override=1785000123)

            # `_collect_environment` probes the suite-selected `ToolchainEnv`
            # rustc and Lean executables across explicit overrides and
            # install-root/cache fallbacks.
            (anneal_dir / "trusted" / "lean").mkdir(parents=True, exist_ok=True)
            (anneal_dir / "trusted" / "lean" / "lean-toolchain").write_text(
                "leanprover/lean4:v4.34.1\n", encoding="utf-8"
            )
            sys_root = root / "sys-a"
            (sys_root / "bin").mkdir(parents=True)
            (sys_root / "lib").mkdir(parents=True)
            (sys_root / "bin" / "rustc").write_text("", encoding="utf-8")
            mvp_lean = root / "mvp-lean"
            mvp_lean.write_text("", encoding="utf-8")
            inst_root = root / "inst-root"
            (inst_root / "rust" / "bin").mkdir(parents=True)
            (inst_root / "rust" / "lib").mkdir(parents=True)
            (inst_root / "rust" / "bin" / "rustc").write_text("", encoding="utf-8")
            (inst_root / "lean" / "bin").mkdir(parents=True)
            (inst_root / "lean" / "bin" / "lean").write_text("", encoding="utf-8")
            xdg_cache = root / "xdg-cache"
            xdg_lean = (
                xdg_cache / "anneal" / "toolchain" / "v1" / "lean" / "bin" / "lean"
            )
            xdg_lean.parent.mkdir(parents=True)
            xdg_lean.write_text("", encoding="utf-8")

            probed: list[tuple[list[str], str]] = []

            def _probe_side_effect(
                args: list[str],
                *,
                env: dict[str, str] | None = None,
                **_kwargs: object,
            ) -> mock.Mock:
                probed.append((list(args), (env or {}).get("LD_LIBRARY_PATH", "")))
                return mock.Mock(returncode=0, stdout=f"{args[0]} 1.0.0\n", stderr="")

            with mock.patch("subprocess.run", side_effect=_probe_side_effect):
                with mock.patch.dict(
                    os.environ,
                    {
                        "RUSTC": "/ambient/rustc",
                        "ANNEAL_SYSROOT": str(sys_root),
                        "ANNEAL_MVP_LEAN": str(mvp_lean),
                    },
                    clear=True,
                ):
                    env1 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(env1["rustc_version"], f"{sys_root / 'bin' / 'rustc'} 1.0.0")
                self.assertEqual(env1["lean_version"], f"{mvp_lean} 1.0.0")
                self.assertIn(str(sys_root / "lib"), probed[0][1])

                probed.clear()
                with mock.patch.dict(
                    os.environ,
                    {
                        "ANNEAL_TEST_INSTALL_ROOT": str(inst_root),
                    },
                    clear=True,
                ):
                    env2 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(
                    env2["rustc_version"],
                    f"{inst_root / 'rust' / 'bin' / 'rustc'} 1.0.0",
                )
                self.assertEqual(
                    env2["lean_version"],
                    f"{inst_root / 'lean' / 'bin' / 'lean'} 1.0.0",
                )

                probed.clear()
                with mock.patch.dict(
                    os.environ,
                    {
                        "XDG_CACHE_HOME": str(xdg_cache),
                    },
                    clear=True,
                ):
                    env3 = cmd._collect_environment(anneal_dir, caller_cwd=root)
                self.assertEqual(env3["lean_version"], f"{xdg_lean} 1.0.0")

        docs_path = (
            Path(__file__).resolve().parents[2] / "docs" / "perf-tracking.md"
        )
        docs_text = docs_path.read_text(encoding="utf-8")
        self.assertIn(
            'One of `"ms"`, `"KiB"`, `"B"`, `"count"`, `"%"`.', docs_text
        )
