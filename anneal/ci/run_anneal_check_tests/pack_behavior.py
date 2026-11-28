# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Behavior tests for `pack_omnibus_archive.sh`, run against
`PackArchiveFixture`."""

import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile

from run_anneal_check_tests.support import PACK_SCRIPT, CHECK_BUNDLE_TREE


class PackOmnibusArchiveBehaviorCases:
    def test_linux_archive_pack_exclusions_dedup_and_single_pass_verification(self) -> None:
        self._require_tools("zstd", "jq")
        with tempfile.TemporaryDirectory(prefix="anneal-pack-linux-") as tmp:
            root = Path(tmp)
            fix = self.build_fixture(root, platform="linux")
            out_archive = root / "omnibus.tar.zst"
            res = self.run_pack(fix, platform="linux", output_archive=out_archive)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertIn(
                "Verified all 4 library-lock.json sysroot tree digests in archive.",
                res.stdout,
            )
            self.assertTrue(out_archive.is_file())

            decompressed = subprocess.run(
                ["zstd", "-dc", str(out_archive)],
                capture_output=True,
                check=True,
            ).stdout
            import io

            members: dict[str, tarfile.TarInfo] = {}
            contents: dict[str, bytes] = {}
            with tarfile.open(fileobj=io.BytesIO(decompressed), mode="r:") as tf:
                for m in tf.getmembers():
                    name = m.name.rstrip("/")
                    members[name] = m
                    self.assertEqual(m.mtime, 0, name)
                    self.assertEqual(m.uid, 0, name)
                    self.assertEqual(m.gid, 0, name)
                    if m.isreg():
                        fobj = tf.extractfile(m)
                        assert fobj is not None
                        contents[name] = fobj.read()

            # Excluded payloads must be absent.
            for forbidden in (
                "lean/bin/lake",
                "lean/lib/libfoo.a",
                "lean/lib/lean/Init.ilean",
                "lean/src/lean/Lean.lean",
                "rust/bin/miri",
                "rust/share/doc/readme.txt",
                "rust/lib/rustlib/src/rust/library/core/src/lib.rs",
                f"rust/lib/rustlib/{self.RUST_TARGET}/bin/llc",
                f"rust/lib/rustlib/{self.RUST_TARGET}/bin/rust-objcopy",
                "share/anneal/theory/Anneal/Canaries.lean",
                "share/anneal/theory/Anneal.lean",
                "share/anneal/prebuilt/lib/Anneal.olean",
            ):
                self.assertNotIn(forbidden, members)

            for required in (
                "share/anneal/trusted/audit/SpecPreflight.lean",
                "share/anneal/prebuilt/SpecPreflight.olean",
                "share/anneal/theory/Anneal/MirWp.lean",
                "share/anneal/theory/Anneal/Scalar.lean",
                "share/anneal/theory/Anneal/Wp.lean",
                "share/anneal/prebuilt/lib/Anneal/MirWp.olean",
                "share/anneal/prebuilt/lib/Anneal/Scalar.olean",
                "share/anneal/prebuilt/lib/Anneal/Wp.olean",
            ):
                self.assertIn(required, members)

            # Duplicate byte-identical `libLLVM` and `librustc_driver-` are
            # symlinked.
            for lib_name in ("libLLVM-21.so", "librustc_driver-deadbeef.so"):
                rel = f"rust/lib/rustlib/{self.RUST_TARGET}/lib/{lib_name}"
                self.assertIn(rel, members)
                self.assertTrue(members[rel].issym(), rel)
                self.assertEqual(members[rel].linkname, f"../../../{lib_name}")

            # Runtime libs come from `--libz` / `--libgcc-s`, not stale rust
            # copies.
            expected_libz = fix["libz"].read_bytes()
            expected_libgcc = fix["libgcc"].read_bytes()
            self.assertTrue(expected_libz.endswith(b"canonical-runtime-libz"))
            self.assertTrue(expected_libgcc.endswith(b"canonical-runtime-libgcc"))
            self.assertNotEqual(
                expected_libz, (fix["rust_tc"] / "lib/libz.so.1").read_bytes()
            )
            self.assertNotEqual(
                expected_libgcc, (fix["rust_tc"] / "lib/libgcc_s.so.1").read_bytes()
            )
            self.assertEqual(contents["rust/lib/libz.so.1"], expected_libz)
            self.assertEqual(contents["rust/lib/libgcc_s.so.1"], expected_libgcc)

            # `patchelf` added `libz.so.1` when absent from `--print-needed`.
            patchelf_calls = fix["patchelf_log"].read_text(encoding="utf-8")
            self.assertIn("--print-needed", patchelf_calls)
            self.assertIn("--add-needed libz.so.1", patchelf_calls)
            self.assertIn("--set-rpath $ORIGIN/../rust/lib", patchelf_calls)

    def test_linux_fixture_rust_lib_is_ld_so_loadable_under_ld_library_path(self) -> None:
        with tempfile.TemporaryDirectory(prefix="anneal-pack-ldso-") as tmp:
            root = Path(tmp)
            fix = self.build_fixture(root, platform="linux")
            rust_lib = fix["rust_tc"] / "lib"
            env = dict(os.environ, LD_LIBRARY_PATH=str(rust_lib))
            env_res = subprocess.run(
                ["/usr/bin/env", "true"],
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(env_res.returncode, 0, env_res.stderr)
            rustc_res = subprocess.run(
                [str(fix["rust_tc"] / "bin/rustc"), "-vV"],
                env=env,
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(rustc_res.returncode, 0, rustc_res.stderr)
            self.assertIn(f"host: {self.RUST_TARGET}", rustc_res.stdout)
            if sys.platform.startswith("linux"):
                dlopen_res = subprocess.run(
                    [
                        sys.executable,
                        "-I",
                        "-B",
                        "-c",
                        "import ctypes, sys\n"
                        "for p in sys.argv[1:]:\n"
                        "    ctypes.CDLL(p)\n",
                        str(rust_lib / "libgcc_s.so.1"),
                        str(rust_lib / "libz.so.1"),
                        str(fix["libgcc"]),
                        str(fix["libz"]),
                    ],
                    capture_output=True,
                    text=True,
                    check=False,
                )
                self.assertEqual(dlopen_res.returncode, 0, dlopen_res.stderr)

    def test_patchelf_skips_add_needed_when_libz_already_present(self) -> None:
        self._require_tools("jq")
        with tempfile.TemporaryDirectory(prefix="anneal-pack-patchelf-") as tmp:
            root = Path(tmp)
            fix = self.build_fixture(
                root, platform="linux", capture_already_needs_libz=True
            )
            stage_dir = root / "staged"
            res = self.run_pack(fix, platform="linux", stage_dir=stage_dir)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            patchelf_calls = fix["patchelf_log"].read_text(encoding="utf-8")
            self.assertIn("--print-needed", patchelf_calls)
            self.assertNotIn("--add-needed libz.so.1", patchelf_calls)
            self.assertIn("--set-rpath $ORIGIN/../rust/lib", patchelf_calls)

    def test_relative_work_and_toolchain_dirs_succeed_with_dedup_symlinks(self) -> None:
        self._require_tools("zstd", "jq")
        with tempfile.TemporaryDirectory(prefix="anneal-pack-relwork-") as tmp:
            root = Path(tmp)
            fix = self.build_fixture(root, platform="linux")
            cmd = [
                "bash",
                str(PACK_SCRIPT),
                "--platform",
                "linux",
                "--anneal-root",
                "anneal",
                "--rust-toolchain",
                "nix-rust-toolchain",
                "--lean-toolchain",
                "nix-lean-toolchain",
                "--lean-exec",
                "./build-lean",
                "--rustc-capture-bin",
                "./anneal-rustc-capture",
                "--libz",
                "runtime-libs/libz.so.1",
                "--libgcc-s",
                "runtime-libs/libgcc_s.so.1",
                "--python",
                sys.executable,
                "--work-dir",
                "work/rel-stage",
                "--prebuild-jobs",
                "2",
                "--zstd-jobs",
                "1",
                "--output-archive",
                "omnibus-rel.tar.zst",
            ]
            env = dict(os.environ)
            env["PATH"] = f"{fix['fake_bin']}:{env.get('PATH', '')}"
            res = subprocess.run(
                cmd, cwd=root, env=env, capture_output=True, text=True, check=False
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertTrue((root / "omnibus-rel.tar.zst").is_file())

    def test_darwin_archive_pack_succeeds_without_patchelf_or_linux_libs(self) -> None:
        self._require_tools("zstd", "jq")
        with tempfile.TemporaryDirectory(prefix="anneal-pack-darwin-") as tmp:
            root = Path(tmp)
            fix = self.build_fixture(
                root, platform="darwin", rust_target="aarch64-apple-darwin"
            )
            out_archive = root / "omnibus-darwin.tar.zst"
            res = self.run_pack(
                fix,
                platform="darwin",
                rust_target="aarch64-apple-darwin",
                output_archive=out_archive,
            )
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)
            self.assertFalse(fix["patchelf_log"].exists())
            darwin_calls = fix["darwin_log"].read_text(encoding="utf-8")
            self.assertIn(
                "install_name_tool -change /nix/store/abc-libiconv/lib/libiconv.2.dylib "
                "/usr/lib/libiconv.2.dylib",
                darwin_calls,
            )
            self.assertIn(
                "install_name_tool -change /nix/store/def-zlib/lib/libz.dylib "
                "/usr/lib/libz.1.dylib",
                darwin_calls,
            )
            self.assertIn(
                "install_name_tool -delete_rpath /nix/store/abc-rustc/lib",
                darwin_calls,
            )
            self.assertIn(
                "install_name_tool -add_rpath @executable_path/../rust/lib",
                darwin_calls,
            )
            self.assertIn("codesign -s - --force", darwin_calls)

    def test_stage_dir_mode_skips_archive_and_passes_check_bundle_tree(self) -> None:
        self._require_tools("jq")
        with tempfile.TemporaryDirectory(prefix="anneal-stage-dir-") as tmp:
            root = Path(tmp)
            fix = self.build_fixture(root, platform="linux")
            cache_root = root / "cache"
            stage_dir = cache_root / "anneal" / "toolchain" / "extracted"
            res = self.run_pack(fix, platform="linux", stage_dir=stage_dir)
            self.assertEqual(res.returncode, 0, res.stdout + res.stderr)

            self.assertTrue((stage_dir / "bin/anneal-rustc-capture").is_file())
            self.assertTrue(
                (stage_dir / "share/anneal/trusted/audit/SpecPreflight.lean").is_file()
            )
            self.assertTrue(
                (stage_dir / "share/anneal/prebuilt/SpecPreflight.olean").is_file()
            )
            self.assertFalse((stage_dir / "lean/bin/lake").exists())
            self.assertFalse((stage_dir / "rust/bin/miri").exists())
            self.assertFalse((stage_dir / "share/anneal/theory/Anneal/Canaries.lean").exists())
            llvm_link = stage_dir / f"rust/lib/rustlib/{self.RUST_TARGET}/lib/libLLVM-21.so"
            self.assertTrue(llvm_link.is_symlink())
            self.assertEqual(os.readlink(llvm_link), "../../../libLLVM-21.so")
            self.assertEqual(
                (stage_dir / "rust/lib/libz.so.1").read_bytes(),
                fix["libz"].read_bytes(),
            )
            self.assertTrue(
                (stage_dir / "rust/lib/libz.so.1")
                .read_bytes()
                .endswith(b"canonical-runtime-libz")
            )

            # Verify the staged directory satisfies `check_bundle_tree.py`
            # end-to-end.
            chk = subprocess.run(
                [
                    sys.executable,
                    "-I",
                    "-B",
                    str(CHECK_BUNDLE_TREE),
                    "--cache-root",
                    str(cache_root),
                    "--root",
                    str(stage_dir),
                ],
                capture_output=True,
                text=True,
                check=False,
            )
            self.assertEqual(chk.returncode, 0, chk.stdout + chk.stderr)
            self.assertIn(f"ANNEAL_TEST_INSTALL_ROOT={stage_dir.resolve()}", chk.stdout)

    def test_negative_invariants_fail_closed(self) -> None:
        self._require_tools("zstd", "jq")
        cases = [
            (
                "forbidden_manifest_canary",
                "linux",
                {"manifest_extra_paths": ["theory/Anneal/Canaries.lean"]},
                "forbidden bundle-manifest path",
            ),
            (
                "forbidden_manifest_traversal",
                "linux",
                {"manifest_extra_paths": ["theory/Anneal/../Secret.lean"]},
                "forbidden bundle-manifest path",
            ),
            (
                "tampered_library_lock",
                "linux",
                {"tamper_lock": True},
                "library-lock mismatch",
            ),
            (
                "sysroot_symlink",
                "linux",
                {"plant_sysroot_symlink": True},
                "symlink forbidden in sysroot",
            ),
            (
                "prebuilt_canary_leak",
                "linux",
                {"leak_prebuilt_canary": True},
                "canary module leaked",
            ),
            (
                "prebuilt_umbrella_leak",
                "linux",
                {"leak_prebuilt_umbrella": True},
                "retired monolithic Anneal umbrella leaked",
            ),
            (
                "elf_rpath_nix_store_leak",
                "linux",
                {"leak_elf_rpath_nix_store": True},
                "Nix store reference leaked into ELF header",
            ),
            (
                "elf_unexpected_dt_needed",
                "linux",
                {"extra_elf_needed": "libunexpected.so.1"},
                "unexpected DT_NEEDED dependency libunexpected.so.1",
            ),
            (
                "darwin_unexpected_nix_dylib",
                "darwin",
                {"leak_darwin_nix_dylib": True},
                "unexpected Nix store dylib",
            ),
            (
                "divergent_duplicate_libllvm",
                "linux",
                {"duplicate_llvm_identical": False},
                "duplicate regular-file libLLVM/librustc_driver in archive",
            ),
            (
                "expected_entry_is_directory",
                "linux",
                {"rustdoc_as_dir": True},
                "expected archive entry missing or not a file/symlink",
            ),
        ]
        for label, plat, kwargs, expected_error in cases:
            with self.subTest(case=label):
                with tempfile.TemporaryDirectory(prefix=f"anneal-pack-neg-{label}-") as tmp:
                    root = Path(tmp)
                    fix = self.build_fixture(root, platform=plat, **kwargs)
                    out_archive = root / "omnibus.tar.zst"
                    res = self.run_pack(fix, platform=plat, output_archive=out_archive)
                    self.assertNotEqual(res.returncode, 0, f"{label} unexpectedly passed")
                    self.assertIn(expected_error, res.stderr)

    def test_archive_verifier_rejects_retired_monolithic_umbrella(self) -> None:
        pack_text = PACK_SCRIPT.read_text(encoding="utf-8")
        match = re.search(
            r'cat > "\$work_dir/verify_archive\.py" <<\'PYEOF\'\n(.*?)^PYEOF$',
            pack_text,
            re.M | re.S,
        )
        self.assertIsNotNone(match, "verify_archive.py heredoc not found")
        verifier_code = match.group(1)

        import io

        cases = [
            ("theory_umbrella_file", "share/anneal/theory/Anneal.lean", False),
            ("theory_umbrella_symlink", "share/anneal/theory/Anneal.lean", True),
            ("prebuilt_umbrella_file", "share/anneal/prebuilt/lib/Anneal.olean", False),
            ("prebuilt_umbrella_symlink", "share/anneal/prebuilt/lib/Anneal.olean", True),
        ]
        for label, member_name, as_symlink in cases:
            with self.subTest(case=label):
                with tempfile.TemporaryDirectory(prefix=f"anneal-pack-{label}-") as tmp:
                    root = Path(tmp)
                    fix = self.build_fixture(root, platform="linux")
                    buf = io.BytesIO()
                    with tarfile.open(fileobj=buf, mode="w") as tf:
                        info = tarfile.TarInfo(member_name)
                        if as_symlink:
                            info.type = tarfile.SYMTYPE
                            info.linkname = "Anneal/Wp.lean"
                            tf.addfile(info)
                        else:
                            data = b"-- retired umbrella\n"
                            info.size = len(data)
                            tf.addfile(info, io.BytesIO(data))
                    env = dict(
                        os.environ,
                        OUT_ARCHIVE=str(root / f"{label}.tar.zst"),
                        PLATFORM="linux",
                        RUST_TARGET=self.RUST_TARGET,
                        BUNDLE_MANIFEST=str(fix["anneal"] / "theory/bundle-manifest.json"),
                        STAGED_LIBRARY_LOCK=str(
                            fix["anneal"] / "trusted/audit/library-lock.json"
                        ),
                    )
                    verifier_path = root / "verify_archive.py"
                    verifier_path.write_text(verifier_code, encoding="utf-8")
                    res = subprocess.run(
                        [sys.executable, "-I", "-B", str(verifier_path)],
                        input=buf.getvalue(),
                        env=env,
                        capture_output=True,
                        check=False,
                    )
                    self.assertNotEqual(res.returncode, 0, f"{label} unexpectedly passed")
                    self.assertIn(
                        b"retired monolithic Anneal umbrella leaked",
                        res.stderr,
                    )

    def test_archive_verifier_rejects_duplicate_archive_member(self) -> None:
        pack_text = PACK_SCRIPT.read_text(encoding="utf-8")
        match = re.search(
            r'cat > "\$work_dir/verify_archive\.py" <<\'PYEOF\'\n(.*?)^PYEOF$',
            pack_text,
            re.M | re.S,
        )
        self.assertIsNotNone(match, "verify_archive.py heredoc not found")
        verifier_code = match.group(1)

        import io

        with tempfile.TemporaryDirectory(prefix="anneal-pack-dup-member-") as tmp:
            root = Path(tmp)
            fix = self.build_fixture(root, platform="linux")
            buf = io.BytesIO()
            with tarfile.open(fileobj=buf, mode="w") as tf:
                for _ in range(2):
                    data = b"-- dup\n"
                    info = tarfile.TarInfo("share/anneal/theory/Anneal/MirWp.lean")
                    info.size = len(data)
                    tf.addfile(info, io.BytesIO(data))
            env = dict(
                os.environ,
                OUT_ARCHIVE=str(root / "dup.tar.zst"),
                PLATFORM="linux",
                RUST_TARGET=self.RUST_TARGET,
                BUNDLE_MANIFEST=str(fix["anneal"] / "theory/bundle-manifest.json"),
                STAGED_LIBRARY_LOCK=str(
                    fix["anneal"] / "trusted/audit/library-lock.json"
                ),
            )
            verifier_path = root / "verify_archive.py"
            verifier_path.write_text(verifier_code, encoding="utf-8")
            res = subprocess.run(
                [sys.executable, "-I", "-B", str(verifier_path)],
                input=buf.getvalue(),
                env=env,
                capture_output=True,
                check=False,
            )
            self.assertNotEqual(res.returncode, 0)
            self.assertIn(
                b"duplicate archive entry",
                res.stderr,
            )

    def test_require_tools_fails_under_ci_strict_when_tool_missing(self) -> None:
        from unittest.mock import patch

        with patch.dict(os.environ, {"ANNEAL_CI_STRICT": "1"}):
            with patch.object(shutil, "which", return_value=None):
                with self.assertRaises(AssertionError) as ctx:
                    self._require_tools("zstd", "jq")
        self.assertIn("required tools missing from PATH: zstd, jq", str(ctx.exception))
