# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""`PackArchiveFixture`: the fake toolchain tree, tools, and `run_pack`
driver for the `pack_omnibus_archive.sh` behavior tests."""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

from run_anneal_check_tests.support import PACK_SCRIPT, _tagged_shared_lib_bytes, tree_digest


class PackArchiveFixture:
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
            "vendor/minirust/UPSTREAM_PIN.json": b"{}\n",
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
