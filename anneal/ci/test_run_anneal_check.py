# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Unit and behavioral tests for `run_anneal_check.sh` and `pack_omnibus_archive.sh`.

Both `anneal/flake.nix` and `anneal/ci/run_anneal_check.sh` delegate omnibus
staging, exclusion filtering, `libLLVM`/`librustc_driver` symlink deduplication,
and single-pass archive verification to `anneal/ci/pack_omnibus_archive.sh`.
These tests verify that wiring and exercise `pack_omnibus_archive.sh` directly.
"""

import ctypes
import functools
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import tomllib
import unittest


ANNEAL_ROOT = Path(__file__).resolve().parent.parent
REPO_ROOT = ANNEAL_ROOT.parent
SCRIPT = ANNEAL_ROOT / "ci" / "run_anneal_check.sh"
PACK_SCRIPT = ANNEAL_ROOT / "ci" / "pack_omnibus_archive.sh"
CHECK_BUNDLE_TREE = ANNEAL_ROOT / "ci" / "check_bundle_tree.py"
FLAKE = ANNEAL_ROOT / "flake.nix"
CHECKS_TOML = REPO_ROOT / "ci" / "checks.toml"
ANNEAL_TC_DOCKERFILE = REPO_ROOT / "ci" / "docker" / "anneal-tc.Dockerfile"


def shell_function(text: str, name: str) -> str:
    match = re.search(rf"^{name}\(\) \{{\n.*?^\}}\n", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"function {name} not found")
    return match.group(0)


def case_branch(text: str, label: str) -> str:
    match = re.search(rf"^  {re.escape(label)}\)\n(.*?)^    ;;$", text, re.M | re.S)
    if match is None:
        raise AssertionError(f"case branch {label!r} not found")
    return match.group(1)


@functools.lru_cache(maxsize=None)
def _linux_shared_lib_bytes(soname: str) -> bytes:
    """Return valid host ELF shared-library bytes for `soname` on Linux."""
    if not sys.platform.startswith("linux"):
        return b""
    try:
        ctypes.CDLL(soname)
    except OSError:
        pass
    stem = soname.split(".so", 1)[0] + ".so"
    maps_path = Path("/proc/self/maps")
    if maps_path.is_file():
        for line in maps_path.read_text(encoding="utf-8", errors="replace").splitlines():
            parts = line.strip().split(None, 5)
            if len(parts) < 6 or not parts[5].startswith("/"):
                continue
            cand = Path(parts[5])
            if (cand.name == soname or cand.name.startswith(stem)) and cand.is_file():
                data = cand.read_bytes()
                if data.startswith(b"\x7fELF"):
                    return data
    for lib_dir in (
        "/lib/x86_64-linux-gnu",
        "/usr/lib/x86_64-linux-gnu",
        "/lib/aarch64-linux-gnu",
        "/usr/lib/aarch64-linux-gnu",
        "/lib64",
        "/usr/lib64",
        "/lib",
        "/usr/lib",
    ):
        cand = Path(lib_dir) / soname
        if cand.is_file():
            data = cand.read_bytes()
            if data.startswith(b"\x7fELF"):
                return data
    return b""


def _tagged_shared_lib_bytes(soname: str, tag: bytes, *, platform: str) -> bytes:
    prefix = _linux_shared_lib_bytes(soname) if platform == "linux" else b""
    return (prefix + b"\n" + tag) if prefix else tag


def tree_digest(tree_dir: Path) -> str:
    files = []
    for cur, _dirs, names in os.walk(tree_dir, followlinks=False):
        cur_p = Path(cur)
        for name in names:
            fp = cur_p / name
            files.append((fp.relative_to(tree_dir).as_posix(), fp))
    files.sort(key=lambda item: item[0].encode("utf-8"))
    h = hashlib.sha256()
    for rel, fp in files:
        fh = hashlib.sha256(fp.read_bytes())
        h.update(rel.encode("utf-8"))
        h.update(b"\0")
        h.update(fh.digest())
    return h.hexdigest()


class OmnibusPackWiringTests(unittest.TestCase):
    def setUp(self) -> None:
        self.flake_text = FLAKE.read_text(encoding="utf-8")
        self.script_text = SCRIPT.read_text(encoding="utf-8")
        self.pack_text = PACK_SCRIPT.read_text(encoding="utf-8")

    def test_pack_script_is_executable_and_single_pass_verified(self) -> None:
        mode = PACK_SCRIPT.stat().st_mode
        self.assertTrue(mode & stat.S_IXUSR, "pack_omnibus_archive.sh must be executable")
        self.assertEqual(
            self.pack_text.count("zstd -dc "),
            1,
            "archive verification must decompress the .tar.zst in a single pass",
        )
        self.assertIn("-12 --long=27", self.pack_text)

    def test_flake_and_run_script_both_invoke_canonical_pack_script(self) -> None:
        start = self.flake_text.index("omnibus-archive = pkgs.stdenv.mkDerivation {")
        end = self.flake_text.index("release-check-python =", start)
        omnibus_section = self.flake_text[start:end]

        self.assertIn("packOmnibusScript = ./ci/pack_omnibus_archive.sh;", omnibus_section)
        self.assertIn("targetSpecPreflight = ./trusted/audit/SpecPreflight.lean;", omnibus_section)
        self.assertIn('--target-spec-preflight "$targetSpecPreflight"', omnibus_section)
        self.assertIn('bash "$packOmnibusScript"', omnibus_section)
        self.assertIn("darwin.cctools", omnibus_section)
        self.assertIn("darwin.sigtool", omnibus_section)
        self.assertNotIn("--exclude=", omnibus_section)
        self.assertNotIn("excluded_patterns", omnibus_section)
        self.assertNotIn("zstd -dc", omnibus_section)

        self.assertIn("./ci/pack_omnibus_archive.sh", self.script_text)
        self.assertNotIn("--exclude=", self.script_text)
        self.assertNotIn("excluded_patterns", self.script_text)
        self.assertNotIn("zstd -dc", self.script_text)

    def test_ws_test_stages_directly_while_installed_smoke_packs_archive(self) -> None:
        ci_tests_mode = case_branch(self.script_text, "ci-tests")
        clippy_mode = case_branch(self.script_text, "clippy")
        ws_test = case_branch(self.script_text, "ws-test")
        ws_meta = case_branch(self.script_text, "ws-meta")
        installed_smoke = case_branch(self.script_text, "installed-smoke")

        self.assertIn("export ANNEAL_CI_STRICT=1", ci_tests_mode)
        self.assertIn("--test cli --test inspect", clippy_mode)
        self.assertIn("--lib --target wasm32-unknown-unknown", clippy_mode)

        self.assertIn('stage_ws_toolchain_root "$INSTALL_ROOT"', ws_test)
        self.assertNotIn("build_omnibus_archive", ws_test)
        self.assertNotIn("--zstd", ws_test)
        self.assertNotIn('SHARD_SPEC" == 1/*', ws_test)

        for cmd_fragment in (
            "--example regenerate_bundle",
            "-p cargo-anneal --no-default-features",
            "-p cargo-anneal-tests --no-default-features",
            "--test cli --test inspect",
            "cargo test --workspace --locked --offline",
            "--doc",
        ):
            self.assertIn(cmd_fragment, ws_meta)
            self.assertNotIn(cmd_fragment, ws_test)

        self.assertIn('build_omnibus_archive "$ARCHIVE_PATH"', installed_smoke)
        self.assertIn('setup --local-archive "$ARCHIVE_PATH"', installed_smoke)
        self.assertIn("./bundled_resources.rs", installed_smoke)
        self.assertIn("./bundled_theory.json", installed_smoke)

    def test_ws_meta_preserves_internal_lean_symlinks(self) -> None:
        ws_meta = case_branch(self.script_text, "ws-meta")
        self.assertNotIn("cp -rL", ws_meta)
        self.assertIn('LEAN_TC="$(readlink -f /opt/anneal-nix/lean-toolchain)"', ws_meta)
        self.assertIn('cp -r "$LEAN_TC" "$INSTALL_ROOT/lean"', ws_meta)
        self.assertIn('chmod -R u+w "$INSTALL_ROOT/lean"', ws_meta)

        start = ws_meta.index('    INSTALL_CACHE="')
        end = ws_meta.index('    apply_bundle_env ')
        stage_snippet = ws_meta[start:end]

        with tempfile.TemporaryDirectory() as tmp:
            tmp_path = Path(tmp)
            lean_store = tmp_path / "nix-store-lean"
            (lean_store / "bin").mkdir(parents=True)
            (lean_store / "lib").mkdir(parents=True)
            (lean_store / "bin" / "lean").write_text("#!/bin/sh\n")
            (lean_store / "lib" / "libLLVM.so.22.1").write_bytes(b"elf")
            (lean_store / "lib" / "libLLVM.so").symlink_to("libLLVM.so.22.1")
            top_link = tmp_path / "lean-toolchain-link"
            top_link.symlink_to(lean_store)
            scratch_root = tmp_path / "scratch"
            scratch_root.mkdir()

            for root_dir, _, files in os.walk(lean_store):
                for name in files:
                    p = Path(root_dir) / name
                    if not p.is_symlink():
                        p.chmod(0o444)
                Path(root_dir).chmod(0o555)
            try:
                adapted = stage_snippet.replace(
                    "/opt/anneal-nix/lean-toolchain", str(top_link)
                )
                subprocess.run(
                    [
                        "bash",
                        "-euo",
                        "pipefail",
                        "-c",
                        f'export SCRATCH_ROOT="{scratch_root}"\n{adapted}',
                    ],
                    check=True,
                    capture_output=True,
                    text=True,
                )
            finally:
                for root_dir, _, files in os.walk(lean_store, topdown=False):
                    Path(root_dir).chmod(0o755)
                    for name in files:
                        p = Path(root_dir) / name
                        if not p.is_symlink():
                            p.chmod(0o644)

            staged = scratch_root / "anneal-ws-meta-toolchain/anneal/toolchain/extracted/lean"
            self.assertFalse(staged.is_symlink())
            self.assertTrue(staged.is_dir())
            llvm_real = staged / "lib" / "libLLVM.so.22.1"
            llvm_link = staged / "lib" / "libLLVM.so"
            self.assertFalse(llvm_real.is_symlink())
            self.assertTrue(llvm_real.is_file())
            self.assertTrue(stat.S_IMODE(llvm_real.stat().st_mode) & stat.S_IWUSR)
            self.assertTrue(llvm_link.is_symlink())
            self.assertEqual(os.readlink(llvm_link), "libLLVM.so.22.1")

    def test_checks_toml_and_dockerfile_wire_pack_script_and_ws_meta(self) -> None:
        data = tomllib.loads(CHECKS_TOML.read_text(encoding="utf-8"))
        checks = {c["id"]: c for c in data["checks"]}

        flake_eval = checks["anneal-flake-eval"]
        flake_globs = [
            pat
            for inp in flake_eval["inputs"]
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        ]
        self.assertIn("anneal/ci/pack_omnibus_archive.sh", flake_globs)

        ci_tests = checks["anneal-ci-tests"]
        ci_tests_globs = [
            pat
            for inp in ci_tests["inputs"]
            if inp.get("kind") == "glob"
            for pat in inp.get("include", [])
        ]
        self.assertIn("ci/checks.toml", ci_tests_globs)
        self.assertIn("ci/docker/anneal-tc.Dockerfile", ci_tests_globs)

        self.assertIn("anneal-ws-meta", checks)
        ws_meta = checks["anneal-ws-meta"]
        ws_test = checks["anneal-ws-test"]
        self.assertEqual(ws_meta["image"], ws_test["image"])
        self.assertEqual(ws_meta["sandbox"], ws_test["sandbox"])
        self.assertEqual(ws_meta["runner"], ws_test["runner"])
        self.assertEqual(ws_meta["workdir"], ws_test["workdir"])
        self.assertEqual(
            ws_test["inputs"],
            ws_meta["inputs"] + [{"kind": "glob", "include": ["zerocopy/src/**"]}],
        )
        self.assertEqual(ws_meta["command"], ["./ci/run_anneal_check.sh", "ws-meta"])

        dockerfile_text = ANNEAL_TC_DOCKERFILE.read_text(encoding="utf-8")
        self.assertIn("/tmp/anneal-seed/anneal/ci/pack_omnibus_archive.sh", dockerfile_text)


class PackOmnibusArchiveBehaviorTests(unittest.TestCase):
    RUST_TARGET = "x86_64-unknown-linux-gnu"

    def _require_tools(self, *tools: str) -> None:
        missing = [tool for tool in tools if shutil.which(tool) is None]
        if missing:
            msg = f"required tools missing from PATH: {', '.join(missing)}"
            if os.environ.get("ANNEAL_CI_STRICT") == "1":
                self.fail(msg)
            self.skipTest(msg)

    def build_fixture(
        self,
        root: Path,
        *,
        platform: str = "linux",
        rust_target: str | None = None,
        duplicate_llvm_identical: bool = True,
        leak_prebuilt_canary: bool = False,
        leak_prebuilt_umbrella: bool = False,
        manifest_extra_paths: list[str] | None = None,
        tamper_lock: bool = False,
        plant_sysroot_symlink: bool = False,
        capture_already_needs_libz: bool = False,
        leak_elf_rpath_nix_store: bool = False,
        extra_elf_needed: str | None = None,
        leak_darwin_nix_dylib: bool = False,
        rustdoc_as_dir: bool = False,
    ) -> dict[str, Path]:
        target = rust_target or (
            self.RUST_TARGET if platform == "linux" else "aarch64-apple-darwin"
        )
        rust_tc = root / "nix-rust-toolchain"
        lean_tc = root / "nix-lean-toolchain"
        anneal = root / "anneal"
        fake_bin = root / "fake-bin"
        runtime_libs = root / "runtime-libs"
        work_dir = root / "work"

        for d in (rust_tc, lean_tc, anneal, fake_bin, runtime_libs, work_dir):
            d.mkdir(parents=True, exist_ok=True)

        # Stateful fake `patchelf` so Linux ELF rewriting and post-rewrite
        # closure checks run cleanly without host `patchelf` installed.
        patchelf_log = root / "patchelf.log"
        patchelf_state = root / "patchelf_state.json"
        initial_needed = (
            ["libz.so.1", "libc.so.6"]
            if capture_already_needs_libz
            else ["libc.so.6"]
        )
        if extra_elf_needed is not None:
            initial_needed.append(extra_elf_needed)
        patchelf_state.write_text(
            json.dumps(
                {
                    "interp": "/nix/store/fake-glibc/lib/ld-linux-x86-64.so.2",
                    "rpath": "/nix/store/fake-rustc/lib",
                    "needed": initial_needed,
                    "leak_rpath": leak_elf_rpath_nix_store,
                }
            ),
            encoding="utf-8",
        )
        patchelf = fake_bin / "patchelf"
        patchelf.write_text(
            f"#!{sys.executable}\n"
            "import json, sys\n"
            "from pathlib import Path\n"
            f"log = Path({str(patchelf_log)!r})\n"
            f"state_p = Path({str(patchelf_state)!r})\n"
            "args = sys.argv[1:]\n"
            "with log.open('a', encoding='utf-8') as f:\n"
            "    f.write(' '.join(args) + '\\n')\n"
            "st = json.loads(state_p.read_text(encoding='utf-8'))\n"
            "if args[:1] == ['--print-interpreter']:\n"
            "    if args[1].endswith('/rustc'):\n"
            "        print('/lib64/ld-linux-x86-64.so.2')\n"
            "    else:\n"
            "        print(st['interp'])\n"
            "elif args[:1] == ['--print-rpath']:\n"
            "    print('/nix/store/leaked/lib' if st['leak_rpath'] else st['rpath'])\n"
            "elif args[:1] == ['--print-needed']:\n"
            "    for lib in st['needed']:\n"
            "        print(lib)\n"
            "else:\n"
            "    i = 0\n"
            "    while i < len(args):\n"
            "        if args[i] == '--set-interpreter':\n"
            "            st['interp'] = args[i + 1]\n"
            "            i += 2\n"
            "        elif args[i] == '--set-rpath':\n"
            "            st['rpath'] = args[i + 1]\n"
            "            i += 2\n"
            "        elif args[i] == '--add-needed':\n"
            "            st['needed'].append(args[i + 1])\n"
            "            i += 2\n"
            "        else:\n"
            "            i += 1\n"
            "    state_p.write_text(json.dumps(st), encoding='utf-8')\n",
            encoding="utf-8",
        )
        patchelf.chmod(0o755)

        # Stateful fake Darwin Mach-O tools (`otool`, `install_name_tool`,
        # `codesign`) so Darwin Nix-store stripping and closure checks run on
        # Linux CI runners too.
        darwin_log = root / "darwin_tools.log"
        macho_state = root / "macho_state.json"
        initial_dylibs = [
            "/nix/store/abc-libiconv/lib/libiconv.2.dylib",
            "/nix/store/def-zlib/lib/libz.dylib",
            "/usr/lib/libSystem.B.dylib",
        ]
        if leak_darwin_nix_dylib:
            initial_dylibs.append("/nix/store/xyz-extra/lib/libextra.dylib")
        macho_state.write_text(
            json.dumps(
                {
                    "dylibs": initial_dylibs,
                    "rpaths": ["/nix/store/abc-rustc/lib"],
                }
            ),
            encoding="utf-8",
        )
        otool = fake_bin / "otool"
        otool.write_text(
            f"#!{sys.executable}\n"
            "import json, sys\n"
            "from pathlib import Path\n"
            f"log = Path({str(darwin_log)!r})\n"
            f"state_p = Path({str(macho_state)!r})\n"
            "args = sys.argv[1:]\n"
            "with log.open('a', encoding='utf-8') as f:\n"
            "    f.write('otool ' + ' '.join(args) + '\\n')\n"
            "st = json.loads(state_p.read_text(encoding='utf-8'))\n"
            "if args[:1] == ['-L']:\n"
            "    print(f'{args[1]}:')\n"
            "    for d in st['dylibs']:\n"
            "        print(f'\\t{d} (compatibility version 1.0.0, current version 1.0.0)')\n"
            "elif args[:1] == ['-l']:\n"
            "    for idx, rp in enumerate(st['rpaths']):\n"
            "        print(f'Load command {idx}')\n"
            "        print('          cmd LC_RPATH')\n"
            "        print('      cmdsize 48')\n"
            "        print(f'         path {rp} (offset 12)')\n",
            encoding="utf-8",
        )
        otool.chmod(0o755)

        install_name_tool = fake_bin / "install_name_tool"
        install_name_tool.write_text(
            f"#!{sys.executable}\n"
            "import json, sys\n"
            "from pathlib import Path\n"
            f"log = Path({str(darwin_log)!r})\n"
            f"state_p = Path({str(macho_state)!r})\n"
            "args = sys.argv[1:]\n"
            "with log.open('a', encoding='utf-8') as f:\n"
            "    f.write('install_name_tool ' + ' '.join(args) + '\\n')\n"
            "st = json.loads(state_p.read_text(encoding='utf-8'))\n"
            "if args[:1] == ['-change']:\n"
            "    old, new = args[1], args[2]\n"
            "    st['dylibs'] = [new if d == old else d for d in st['dylibs']]\n"
            "elif args[:1] == ['-delete_rpath']:\n"
            "    st['rpaths'] = [rp for rp in st['rpaths'] if rp != args[1]]\n"
            "elif args[:1] == ['-add_rpath']:\n"
            "    st['rpaths'].append(args[1])\n"
            "state_p.write_text(json.dumps(st), encoding='utf-8')\n",
            encoding="utf-8",
        )
        install_name_tool.chmod(0o755)

        codesign = fake_bin / "codesign"
        codesign.write_text(
            f"#!{sys.executable}\n"
            "import sys\n"
            "from pathlib import Path\n"
            f"log = Path({str(darwin_log)!r})\n"
            "with log.open('a', encoding='utf-8') as f:\n"
            "    f.write('codesign ' + ' '.join(sys.argv[1:]) + '\\n')\n",
            encoding="utf-8",
        )
        codesign.chmod(0o755)

        # Synthetic Rust toolchain with both required and excluded payloads.
        # Use `#!/bin/sh` (never `#!/usr/bin/env bash`) and loadable ELF bytes
        # for `libgcc_s.so.1` / `libz.so.1` so `LD_LIBRARY_PATH="$rust_tc/lib"`
        # cannot break `uutils` `/usr/bin/env` or Nix `bash` on Linux runners.
        rustc_bin = rust_tc / "bin" / "rustc"
        rustc_bin.parent.mkdir(parents=True, exist_ok=True)
        rustc_bin.write_text(
            f"#!/bin/sh\necho 'rustc 1.99.0-nightly'\necho 'host: {target}'\n",
            encoding="utf-8",
        )
        rustc_bin.chmod(0o755)
        stale_libz = _tagged_shared_lib_bytes(
            "libz.so.1", b"stale-rust-libz", platform=platform
        )
        stale_libgcc = _tagged_shared_lib_bytes(
            "libgcc_s.so.1", b"stale-rust-libgcc", platform=platform
        )
        rust_files = {
            "bin/cargo": b"cargo-bin",
            "bin/rustdoc": b"rustdoc-bin",
            "bin/miri": b"excluded-miri",
            "bin/cargo-miri": b"excluded-cargo-miri",
            "bin/rust-gdb": b"excluded-gdb",
            "bin/rust-lldb": b"excluded-lldb",
            "share/doc/readme.txt": b"excluded-share",
            "etc/bash_completion.d/cargo": b"excluded-etc",
            "manifest.in": b"excluded-manifest",
            "libexec/rust-analyzer-proc-macro-srv": b"excluded-libexec",
            "lib/libLLVM-21.so": b"llvm-shared-bytes-v1",
            "lib/librustc_driver-deadbeef.so": b"driver-shared-bytes-v1",
            "lib/libz.so.1": stale_libz,
            "lib/libgcc_s.so.1": stale_libgcc,
            "lib/rustlib/src/rust/library/core/src/lib.rs": b"excluded-rust-src",
            "lib/rustlib/rustc-src/rust/compiler/lib.rs": b"excluded-rustc-src",
            "lib/rustlib/etc/gdb_lookup.py": b"excluded-rustlib-etc",
            f"lib/rustlib/{target}/bin/rust-lld": b"lld-bin",
            f"lib/rustlib/{target}/bin/gcc-ld/ld.lld": b"gcc-lld-bin",
            f"lib/rustlib/{target}/bin/llc": b"excluded-llc",
            f"lib/rustlib/{target}/bin/llvm-strip": b"excluded-llvm-strip",
            f"lib/rustlib/{target}/bin/opt": b"excluded-opt",
            f"lib/rustlib/{target}/bin/wasm-component-ld": b"excluded-wasm-ld",
            f"lib/rustlib/{target}/bin/rust-objcopy": b"excluded-rust-objcopy",
            f"lib/rustlib/{target}/lib/librustc-nightly_rt.asan.a": b"excluded-rt-a",
            f"lib/rustlib/{target}/lib/libLLVM-21.so": (
                b"llvm-shared-bytes-v1"
                if duplicate_llvm_identical
                else b"llvm-divergent-bytes-v2"
            ),
            f"lib/rustlib/{target}/lib/librustc_driver-deadbeef.so": b"driver-shared-bytes-v1",
        }
        if rustdoc_as_dir:
            rust_files.pop("bin/rustdoc")
            (rust_tc / "bin" / "rustdoc").mkdir(parents=True, exist_ok=True)
        for rel, content in rust_files.items():
            p = rust_tc / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(content)

        # Synthetic Lean toolchain with 4 pinned sysroot trees + excluded
        # payloads.
        for rel, content in {
            "bin/lean": b"lean-bin",
            "bin/lake": b"excluded-lake",
            "bin/leanchecker": b"excluded-leanchecker",
            "bin/clang": b"excluded-clang",
            "bin/ld.lld": b"excluded-ld-lld",
            "bin/llvm-ar": b"excluded-llvm-ar",
            "bin/leanc": b"excluded-leanc",
            "bin/leanir": b"excluded-leanir",
            "bin/leantar": b"excluded-leantar",
            "bin/cadical": b"excluded-cadical",
            "bin/leanmake": b"excluded-leanmake",
            "include/lean/lean.h": b"excluded-header",
            "lib/clang/19/include/stddef.h": b"excluded-clang-lib",
            "lib/libLLVM.so": b"excluded-lean-llvm",
            "lib/libclang.so": b"excluded-lean-clang",
            "lib/libfoo.a": b"excluded-static-lib",
            "lib/lean/libbar.a": b"excluded-lean-static-lib",
            "lib/lean/Init.olean": b"init-olean",
            "lib/lean/Init.ir": b"init-ir",
            "lib/lean/Init.ilean": b"excluded-init-ilean",
            "lib/lean/Std.ilean": b"excluded-std-ilean",
            "lib/lean/Lean.ilean": b"excluded-lean-ilean",
            "lib/lean/Lean/Core.ilean": b"excluded-lean-core-ilean",
            "lib/lean/Lake.olean": b"excluded-lake-olean",
            "lib/lean/Lake/Build.olean": b"excluded-lake-dir",
            "lib/lean/LakeMain.olean": b"excluded-lakemain",
            "lib/lean/LeanIR.olean": b"excluded-leanir-olean",
            "lib/lean/LeanChecker.olean": b"excluded-leanchecker-olean",
            "lib/lean/Leanc.olean": b"excluded-leanc-olean",
            "lib/lean/libInit_shared.so": b"init-so",
            "lib/lean/libLake_shared.so": b"lake-so",
            "lib/lean/libleanshared.so": b"lean-so",
            "lib/lean/libleanshared_1.so": b"lean-so-1",
            "lib/lean/libleanshared_2.so": b"lean-so-2",
            "lib/lean/Init/Prelude.olean": b"init-prelude-olean",
            "lib/lean/Std/Basic.olean": b"std-basic-olean",
            "src/lean/Init/Prelude.lean": b"-- init prelude\n",
            "src/lean/Std/Basic.lean": b"-- std basic\n",
            "src/lean/lake/Lake.lean": b"excluded-src-lake",
            "src/lean/Lean/Meta.lean": b"excluded-src-lean-dir",
            "src/lean/Lean.lean": b"excluded-src-lean",
            "src/lean/Std.lean": b"excluded-src-std",
            "src/lean/LeanChecker.lean": b"excluded-src-lc",
            "src/lean/LeanIR.lean": b"excluded-src-ir",
            "src/lean/Leanc.lean": b"excluded-src-leanc",
        }.items():
            p = lean_tc / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(content)

        lock_lines = []
        for label in (
            "lean/lib/lean/Init/**",
            "lean/lib/lean/Std/**",
            "lean/src/lean/Init/**",
            "lean/src/lean/Std/**",
        ):
            sub = label[len("lean/") : -3]
            digest = tree_digest(lean_tc / sub)
            if tamper_lock and label == "lean/lib/lean/Init/**":
                digest = "0" * 64
            lock_lines.append(f"{digest}  {label}")

        if plant_sysroot_symlink:
            (lean_tc / "lib/lean/Init/Link.olean").symlink_to("Prelude.olean")

        # Synthetic Anneal source tree.
        modules = [
            {"path": "theory/Anneal/MirWp.lean", "sha256": "a" * 64},
            {"path": "theory/Anneal/Scalar.lean", "sha256": "c" * 64},
            {"path": "theory/Anneal/Wp.lean", "sha256": "d" * 64},
        ]
        if manifest_extra_paths:
            for extra in manifest_extra_paths:
                modules.append({"path": extra, "sha256": "b" * 64})
        for rel, content in {
            "trusted/lean/foundation-lock.json": b"{}\n",
            "trusted/lean/lean-toolchain": b"leanprover/lean4:v4.34.1\n",
            "trusted/lean/Trusted/MirAst.lean": b"-- MirAst\n",
            "trusted/lean/Trusted/MirSemantics.lean": b"-- MirSemantics\n",
            "trusted/audit/SpecPreflight.lean": b"-- SpecPreflight\n",
            "trusted/audit/TrustedBoundary.lean": b"-- TrustedBoundary\n",
            "trusted/audit/library-lock.json": ("\n".join(lock_lines) + "\n").encode("utf-8"),
            "trusted/cargo-anneal/src/trusted_bundle.rs": b"// bundle\n",
            "vendor/lean-miri/UPSTREAM_PIN.json": b"{}\n",
            "trusted/correspondence/adapter.lean": b"-- adapter\n",
            "correspondence/proof.lean": b"-- proof\n",
            "theory/Anneal/MirWp.lean": b"-- MirWp\n",
            "theory/Anneal/Scalar.lean": b"-- Scalar\n",
            "theory/Anneal/Wp.lean": b"-- Wp\n",
            "theory/Anneal/Canaries.lean": b"-- must never enter archive\n",
            "theory/bundle-manifest.json": (
                json.dumps({"schema_version": 1, "modules": modules}) + "\n"
            ).encode("utf-8"),
        }.items():
            p = anneal / rel
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_bytes(content)

        # Stub provenance and prebuild scripts.
        render_script = anneal / "ci" / "render_correspondence_provenance.py"
        render_script.parent.mkdir(parents=True, exist_ok=True)
        render_script.write_text(
            "import argparse, json\n"
            "from pathlib import Path\n"
            "p = argparse.ArgumentParser()\n"
            "p.add_argument('--output', required=True)\n"
            "args, _ = p.parse_known_args()\n"
            "Path(args.output).write_text(json.dumps({'schema_version': 1}) + '\\n')\n",
            encoding="utf-8",
        )
        canary_stmt = (
            "(out / 'lib/Anneal/Canaries.olean').write_bytes(b'canary')\n"
            if leak_prebuilt_canary
            else ""
        )
        umbrella_stmt = (
            "(out / 'lib/Anneal.olean').write_bytes(b'umbrella')\n"
            if leak_prebuilt_umbrella
            else ""
        )
        prebuild_script = anneal / "ci" / "prebuild_bundled_oleans.py"
        prebuild_script.write_text(
            "import argparse, json\n"
            "from pathlib import Path\n"
            "p = argparse.ArgumentParser()\n"
            "p.add_argument('--output-dir', required=True)\n"
            "args, _ = p.parse_known_args()\n"
            "out = Path(args.output_dir)\n"
            "(out / 'lib/Trusted').mkdir(parents=True, exist_ok=True)\n"
            "(out / 'lib/Anneal').mkdir(parents=True, exist_ok=True)\n"
            "(out / 'manifest.json').write_text(json.dumps({'schema_version': 1}) + '\\n')\n"
            "(out / 'SpecPreflight.olean').write_bytes(b'sp-olean')\n"
            "(out / 'TrustedBoundary.olean').write_bytes(b'tb-olean')\n"
            "(out / 'lib/Trusted/MirAst.olean').write_bytes(b'ast-olean')\n"
            "(out / 'lib/Anneal/MirWp.olean').write_bytes(b'wp-olean')\n"
            "(out / 'lib/Anneal/Scalar.olean').write_bytes(b'scalar-olean')\n"
            "(out / 'lib/Anneal/Wp.olean').write_bytes(b'wp-umbrella-olean')\n"
            + canary_stmt
            + umbrella_stmt,
            encoding="utf-8",
        )

        capture_bin = root / "anneal-rustc-capture"
        capture_bin.write_bytes(b"capture-bin")
        capture_bin.chmod(0o755)
        lean_exec = root / "build-lean"
        lean_exec.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        lean_exec.chmod(0o755)

        libz = runtime_libs / "libz.so.1"
        libz.write_bytes(
            _tagged_shared_lib_bytes(
                "libz.so.1", b"canonical-runtime-libz", platform=platform
            )
        )
        libgcc = runtime_libs / "libgcc_s.so.1"
        libgcc.write_bytes(
            _tagged_shared_lib_bytes(
                "libgcc_s.so.1", b"canonical-runtime-libgcc", platform=platform
            )
        )

        return {
            "rust_tc": rust_tc,
            "lean_tc": lean_tc,
            "anneal": anneal,
            "fake_bin": fake_bin,
            "capture_bin": capture_bin,
            "lean_exec": lean_exec,
            "libz": libz,
            "libgcc": libgcc,
            "work_dir": work_dir,
            "patchelf_log": patchelf_log,
            "darwin_log": darwin_log,
        }

    def run_pack(
        self,
        fix: dict[str, Path],
        *,
        platform: str = "linux",
        rust_target: str | None = None,
        output_archive: Path | None = None,
        stage_dir: Path | None = None,
    ) -> subprocess.CompletedProcess[str]:
        cmd = [
            "bash",
            str(PACK_SCRIPT),
            "--platform",
            platform,
            "--anneal-root",
            str(fix["anneal"]),
            "--rust-toolchain",
            str(fix["rust_tc"]),
            "--lean-toolchain",
            str(fix["lean_tc"]),
            "--lean-exec",
            str(fix["lean_exec"]),
            "--rustc-capture-bin",
            str(fix["capture_bin"]),
            "--python",
            sys.executable,
            "--work-dir",
            str(fix["work_dir"]),
            "--prebuild-jobs",
            "2",
            "--zstd-jobs",
            "1",
        ]
        if rust_target is not None:
            cmd.extend(["--rust-target", rust_target])
        if platform == "linux":
            cmd.extend(["--libz", str(fix["libz"]), "--libgcc-s", str(fix["libgcc"])])
        if output_archive is not None:
            cmd.extend(["--output-archive", str(output_archive)])
        if stage_dir is not None:
            cmd.extend(["--stage-dir", str(stage_dir)])
        env = dict(os.environ)
        env["PATH"] = f"{fix['fake_bin']}:{env.get('PATH', '')}"
        return subprocess.run(cmd, env=env, capture_output=True, text=True, check=False)

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


class CargoHomeGuardTests(unittest.TestCase):
    NAMES = ("config", "config.toml", "credentials", "credentials.toml", "bin")
    GUARD_CALL = 'guard_mounted_cargo_home "${CARGO_HOME:-}" /cargo-home'

    def run_guard(self, cargo_home: str, mount: Path) -> subprocess.CompletedProcess[str]:
        text = SCRIPT.read_text(encoding="utf-8")
        functions = shell_function(text, "require_inert_cargo_home") + shell_function(
            text, "guard_mounted_cargo_home"
        )
        return subprocess.run(
            ["bash", "-euo", "pipefail", "-c",
             functions + 'guard_mounted_cargo_home "$1" "$2"',
             "guard", cargo_home, str(mount)],
            capture_output=True,
            text=True,
            check=False,
        )

    @staticmethod
    def seed(path: Path, kind: str) -> None:
        if kind == "file":
            path.write_text("")
        elif kind == "dir":
            path.mkdir()
        else:
            path.symlink_to(path.parent / "missing")

    @staticmethod
    def spellings(root: Path, mount: Path) -> list[str]:
        link = root / "link"
        if not link.exists():
            link.symlink_to(mount, target_is_directory=True)
        return [str(mount), f"{mount}/", f"{mount}//", f"{mount}/.",
                f"{mount}/../{mount.name}", str(link)]

    def test_clean_mount_is_accepted(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            mount = Path(tmp) / "cargo-home"
            (mount / "registry").mkdir(parents=True)
            (mount / ".package-cache").write_text("")
            for cargo_home in self.spellings(Path(tmp), mount):
                with self.subTest(cargo_home=cargo_home):
                    self.assertEqual(self.run_guard(cargo_home, mount).returncode, 0)

    def test_preset_or_adopted_mount_with_steering_entry_is_rejected(self) -> None:
        for name in self.NAMES:
            for kind in ("file", "dir", "dangling-symlink"):
                with tempfile.TemporaryDirectory() as tmp:
                    mount = Path(tmp) / "cargo-home"
                    mount.mkdir()
                    self.seed(mount / name, kind)
                    for cargo_home in self.spellings(Path(tmp), mount):
                        with self.subTest(name=name, kind=kind, cargo_home=cargo_home):
                            result = self.run_guard(cargo_home, mount)
                            self.assertEqual(result.returncode, 1)
                            self.assertIn(f"it contains {name}", result.stderr)

    def test_other_cargo_home_does_not_inspect_mount(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            mount = Path(tmp) / "cargo-home"
            mount.mkdir()
            (mount / "config.toml").write_text("")
            other = Path(tmp) / "other"
            other.mkdir()
            for cargo_home in ("", str(other), f"{mount}-2"):
                with self.subTest(cargo_home=cargo_home):
                    self.assertEqual(self.run_guard(cargo_home, mount).returncode, 0)

    def test_guard_runs_once_cargo_home_is_final(self) -> None:
        lines = SCRIPT.read_text(encoding="utf-8").splitlines()
        calls = [i for i, line in enumerate(lines) if line == self.GUARD_CALL]
        self.assertEqual(len(calls), 1)
        exports = [i for i, line in enumerate(lines)
                   if re.match(r"\s*export CARGO_HOME=", line)]
        first_use = lines.index('case "$MODE" in')
        self.assertTrue(exports)
        self.assertLess(max(exports), calls[0])
        self.assertLess(calls[0], first_use)


class PreparedCrateExtractionTests(unittest.TestCase):
    def program(self) -> str:
        text = SCRIPT.read_text(encoding="utf-8")
        match = re.search(
            r"PREPARED_MANIFEST=\"\$\(/usr/bin/python3 -I -B - <<'PY'\n"
            r"(.*?)^PY$",
            text,
            re.M | re.S,
        )
        if match is None:
            raise AssertionError("prepared-crate extraction program not found")
        return match.group(1)

    def run_extract(self, root: Path, seed) -> tuple[subprocess.CompletedProcess[str], Path]:
        diag = root / "diag"
        target = root / "target"
        prepared = target / "package"
        diag.mkdir()
        prepared.mkdir(parents=True)
        (diag / "package-metadata.json").write_text(json.dumps(
            {"packages": [{"name": "cargo-anneal", "version": "9.9.9"}]}
        ))
        src = root / "src" / "cargo-anneal-9.9.9"
        src.mkdir(parents=True)
        (src / "Cargo.toml").write_text("[package]\n")
        with tarfile.open(prepared / "cargo-anneal-9.9.9.crate", "w:gz") as tf:
            tf.add(src, arcname="cargo-anneal-9.9.9")
        seed(prepared / "cargo-anneal-9.9.9")
        env = dict(os.environ, ANNEAL_TEST_DIAGNOSTICS=str(diag),
                   CARGO_TARGET_DIR=str(target))
        result = subprocess.run(
            [sys.executable, "-I", "-B", "-"],
            input=self.program(),
            capture_output=True,
            text=True,
            env=env,
            check=False,
        )
        return result, prepared / "cargo-anneal-9.9.9"

    def test_stale_extraction_is_removed(self) -> None:
        def seed(extracted: Path) -> None:
            extracted.mkdir()
            (extracted / "stale.rs").write_text("")

        with tempfile.TemporaryDirectory() as tmp:
            result, extracted = self.run_extract(Path(tmp), seed)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(result.stdout.strip(), str(extracted / "Cargo.toml"))
            self.assertFalse((extracted / "stale.rs").exists())
            self.assertTrue((extracted / "Cargo.toml").is_file())

    def test_symlinked_extraction_is_replaced(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            outside = Path(tmp) / "outside"
            outside.mkdir()
            (outside / "stale.rs").write_text("")

            def seed(extracted: Path) -> None:
                extracted.symlink_to(outside, target_is_directory=True)

            result, extracted = self.run_extract(Path(tmp), seed)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertFalse(extracted.is_symlink())
            self.assertTrue((extracted / "Cargo.toml").is_file())
            self.assertTrue((outside / "stale.rs").is_file())


class ModeTimeoutTests(unittest.TestCase):
    """Pin the per-mode limit table and the `timeout` re-exec guard."""

    LIMITS = {
        "ws-test": 5400,
        "audit": 5400,
        "installed-smoke": 5400,
        "guard-mutation": 5400,
        "clippy": 1800,
        "flake-eval": 1800,
        "ci-tests": 1800,
        "sandbox": 1800,
        "ws-meta": 1800,
    }
    FUNCTIONS = ("check_timeout_secs", "report_sigterm", "reexec_under_timeout")
    # Each driver mode runs after the guard, standing in for a real mode.
    DRIVER_BODY = """
case "$1" in
  hang) sleep 60 ;;
  ignore-term) trap '' TERM; sleep 60 ;;
  exit7) exit 7 ;;
  self-kill) kill -USR1 "$$" ;;
  env)
    echo "active=${ANNEAL_CHECK_TIMEOUT_ACTIVE-unset}"
    echo "args=$*"
    ;;
esac
"""

    def limit(self, mode: str) -> int:
        text = SCRIPT.read_text(encoding="utf-8")
        result = subprocess.run(
            ["bash", "-euo", "pipefail", "-c",
             shell_function(text, "check_timeout_secs") + 'check_timeout_secs "$1"',
             "limit", mode],
            capture_output=True, text=True, check=True,
        )
        return int(result.stdout)

    def run_driver(self, args: list[str], *, kill_after: str = "120s",
                   env_extra: dict[str, str] | None = None,
                   ) -> subprocess.CompletedProcess[str]:
        text = SCRIPT.read_text(encoding="utf-8")
        functions = "".join(shell_function(text, name) for name in self.FUNCTIONS)
        self.assertIn("--kill-after=120s", functions)
        functions = functions.replace("--kill-after=120s", f"--kill-after={kill_after}")
        env = {k: v for k, v in os.environ.items()
               if not k.startswith("ANNEAL_CHECK_TIMEOUT")}
        env.update(env_extra or {})
        with tempfile.TemporaryDirectory() as tmp:
            driver = Path(tmp) / "driver.sh"
            driver.write_text(
                "#!/usr/bin/env bash\nset -euo pipefail\n" + functions
                + 'reexec_under_timeout "$@"\n' + self.DRIVER_BODY,
                encoding="utf-8",
            )
            return subprocess.run(
                ["bash", str(driver), *args], capture_output=True, text=True,
                env=env, timeout=50, check=False,
            )

    def test_limit_table(self) -> None:
        for mode, secs in self.LIMITS.items():
            with self.subTest(mode=mode):
                self.assertEqual(self.limit(mode), secs)
        self.assertEqual(self.limit("some-future-mode"), 1800)

    def test_every_dispatched_mode_has_explicit_limit(self) -> None:
        text = SCRIPT.read_text(encoding="utf-8")
        dispatch = text[text.index('\ncase "$MODE" in\n'):]
        modes = set(re.findall(r"^  ([a-z][a-z-]*)\)$", dispatch, re.M))
        self.assertEqual(modes, set(self.LIMITS))
        table = shell_function(text, "check_timeout_secs")
        for mode in modes:
            with self.subTest(mode=mode):
                self.assertRegex(table, rf"[ |]{re.escape(mode)}[|)]")

    def test_guard_runs_before_any_work(self) -> None:
        lines = SCRIPT.read_text(encoding="utf-8").splitlines()
        call = lines.index('reexec_under_timeout "$@"')
        self.assertEqual(lines.count('reexec_under_timeout "$@"'), 1)
        self.assertLess(call, lines.index('MODE="$1"'))
        self.assertLess(call, next(i for i, line in enumerate(lines)
                                   if line.startswith("cd ")))

    def test_guard_execs_timeout_with_kill_after(self) -> None:
        guard = shell_function(SCRIPT.read_text(encoding="utf-8"),
                               "reexec_under_timeout")
        self.assertIn(
            'exec /usr/bin/timeout --verbose --kill-after=120s "${limit}s" \\\n'
            '    "$BASH" "$0" "$@"',
            guard,
        )

    def test_timeout_exits_124_with_clear_message(self) -> None:
        result = self.run_driver(["hang"], env_extra={"ANNEAL_CHECK_TIMEOUT_SECS": "1"})
        self.assertEqual(result.returncode, 124, result.stderr)
        self.assertIn("hang: limit 1s", result.stderr)
        self.assertIn("timeout: sending signal TERM", result.stderr)
        self.assertIn("error: run_anneal_check.sh hang got SIGTERM: its 1s limit",
                      result.stderr)

    def test_term_ignoring_mode_is_killed(self) -> None:
        result = self.run_driver(["ignore-term"], kill_after="1s",
                                 env_extra={"ANNEAL_CHECK_TIMEOUT_SECS": "1"})
        # `timeout` kills its own process group, itself included, so a shell
        # parent sees status 137 and Python sees death by SIGKILL.
        self.assertIn(result.returncode, (137, -9), result.stderr)
        self.assertIn("timeout: sending signal KILL", result.stderr)

    def test_exit_status_and_signal_pass_through(self) -> None:
        result = self.run_driver(["exit7"])
        self.assertEqual(result.returncode, 7, result.stderr)
        result = self.run_driver(["self-kill"])
        self.assertIn(result.returncode, (128 + 10, -10), result.stderr)

    def test_sentinel_is_cleared_and_args_preserved(self) -> None:
        result = self.run_driver(["env", "a b", "c"])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout, "active=unset\nargs=env a b c\n")

    def test_override_may_only_tighten(self) -> None:
        for value in ("1801", "0", "-1", "1e3", "abc", "9999999"):
            with self.subTest(value=value):
                result = self.run_driver(
                    ["exit7"], env_extra={"ANNEAL_CHECK_TIMEOUT_SECS": value})
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("ANNEAL_CHECK_TIMEOUT_SECS must be in 1..1800",
                              result.stderr)


if __name__ == "__main__":
    unittest.main()
