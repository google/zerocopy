#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Empirical ELF DT_RPATH/DT_RUNPATH scope and Nix rust-lld sandbox probe."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent


def read_dynamic_tags(elf_path: Path) -> dict:
    out = subprocess.run(
        ["readelf", "-d", "-l", str(elf_path)],
        check=True,
        capture_output=True,
        text=True,
    ).stdout
    needed = []
    rpath = None
    runpath = None
    interp = None
    for line in out.splitlines():
        if "(NEEDED)" in line and "[" in line:
            needed.append(line.split("[", 1)[1].split("]", 1)[0])
        elif "(RPATH)" in line and "[" in line:
            rpath = line.split("[", 1)[1].split("]", 1)[0]
        elif "(RUNPATH)" in line and "[" in line:
            runpath = line.split("[", 1)[1].split("]", 1)[0]
        elif "Requesting program interpreter:" in line:
            interp = line.split("Requesting program interpreter:", 1)[1].split("]", 1)[0].strip()
    return {
        "interp": interp,
        "needed": needed,
        "dt_rpath": rpath,
        "dt_runpath": runpath,
    }


def run_synthetic_five_cell_matrix(tmp: Path) -> list[dict]:
    """Build a 3-tier shared-library chain (main -> libmid -> libleaf -> libdep)
    and test all 5 DT_RUNPATH / DT_RPATH / --add-needed / co-location cells.
    """
    src_dir = tmp / "src"
    src_dir.mkdir(parents=True, exist_ok=True)
    (src_dir / "dep.c").write_text("int dep_val(void) { return 42; }\n")
    (src_dir / "leaf.c").write_text(
        "extern int dep_val(void);\nint leaf_val(void) { return dep_val() + 1; }\n"
    )
    (src_dir / "mid.c").write_text(
        "extern int leaf_val(void);\nint mid_val(void) { return leaf_val() + 1; }\n"
    )
    (src_dir / "main.c").write_text(
        '#include <stdio.h>\nextern int mid_val(void);\nint main(void) { printf("%d\\n", mid_val()); return 0; }\n'
    )

    cells = []

    def build_base_tree(cell_dir: Path, leaf_uses_runpath: bool) -> tuple[Path, Path, Path]:
        bin_dir = cell_dir / "bin"
        lib_main = cell_dir / "lib_main"
        lib_dep = cell_dir / "lib_dep"
        bin_dir.mkdir(parents=True, exist_ok=True)
        lib_main.mkdir(parents=True, exist_ok=True)
        lib_dep.mkdir(parents=True, exist_ok=True)

        subprocess.run(
            ["cc", "-shared", "-fPIC", str(src_dir / "dep.c"), "-Wl,-soname,libdep.so", "-o", str(lib_dep / "libdep.so")],
            check=True,
        )
        leaf_dtags_flag = "-Wl,--enable-new-dtags" if leaf_uses_runpath else "-Wl,--disable-new-dtags"
        subprocess.run(
            [
                "cc",
                "-shared",
                "-fPIC",
                str(src_dir / "leaf.c"),
                "-L",
                str(lib_dep),
                "-ldep",
                "-Wl,-soname,libleaf.so",
                leaf_dtags_flag,
                "-Wl,-rpath,$ORIGIN",
                "-o",
                str(lib_main / "libleaf.so"),
            ],
            check=True,
        )
        subprocess.run(
            [
                "cc",
                "-shared",
                "-fPIC",
                str(src_dir / "mid.c"),
                "-L",
                str(lib_main),
                "-lleaf",
                "-Wl,-soname,libmid.so",
                "-Wl,--enable-new-dtags",
                "-Wl,-rpath,$ORIGIN",
                "-o",
                str(lib_main / "libmid.so"),
            ],
            check=True,
        )
        return bin_dir, lib_main, lib_dep

    # Cell 1: main_bin has DT_RUNPATH = $ORIGIN/../lib_main:$ORIGIN/../lib_dep; libleaf has DT_RUNPATH = $ORIGIN.
    c1 = tmp / "cell1"
    bin_dir, lib_main, lib_dep = build_base_tree(c1, leaf_uses_runpath=True)
    main1 = bin_dir / "main"
    subprocess.run(
        [
            "cc",
            str(src_dir / "main.c"),
            "-L",
            str(lib_main),
            "-lmid",
            f"-Wl,-rpath-link,{lib_main}:{lib_dep}",
            "-Wl,--enable-new-dtags",
            "-Wl,-rpath,$ORIGIN/../lib_main:$ORIGIN/../lib_dep",
            "-o",
            str(main1),
        ],
        check=True,
    )
    res1 = subprocess.run(["env", "-i", str(main1)], capture_output=True, text=True)
    cells.append(
        {
            "cell": "1_main_runpath_leaf_runpath_uncolocated",
            "main_tags": read_dynamic_tags(main1),
            "leaf_tags": read_dynamic_tags(lib_main / "libleaf.so"),
            "exit_code": res1.returncode,
            "stdout": res1.stdout.strip(),
            "stderr_contains_libdep_missing": "libdep.so: cannot open shared object file" in res1.stderr,
        }
    )

    # Cell 2: main_bin has DT_RPATH (0x0f, --disable-new-dtags); libleaf STILL has DT_RUNPATH = $ORIGIN.
    # Proves that libleaf's DT_RUNPATH != NULL suppresses _dl_map_object's ancestor DT_RPATH walk!
    c2 = tmp / "cell2"
    bin_dir, lib_main, lib_dep = build_base_tree(c2, leaf_uses_runpath=True)
    main2 = bin_dir / "main"
    subprocess.run(
        [
            "cc",
            str(src_dir / "main.c"),
            "-L",
            str(lib_main),
            "-lmid",
            f"-Wl,-rpath-link,{lib_main}:{lib_dep}",
            "-Wl,--disable-new-dtags",
            "-Wl,-rpath,$ORIGIN/../lib_main:$ORIGIN/../lib_dep",
            "-o",
            str(main2),
        ],
        check=True,
    )
    res2 = subprocess.run(["env", "-i", str(main2)], capture_output=True, text=True)
    cells.append(
        {
            "cell": "2_main_rpath_blocked_by_leaf_runpath",
            "main_tags": read_dynamic_tags(main2),
            "leaf_tags": read_dynamic_tags(lib_main / "libleaf.so"),
            "exit_code": res2.returncode,
            "stdout": res2.stdout.strip(),
            "stderr_contains_libdep_missing": "libdep.so: cannot open shared object file" in res2.stderr,
        }
    )

    # Cell 3: main_bin has DT_RPATH (0x0f) AND libleaf uses DT_RPATH (no DT_RUNPATH).
    # Now loader->l_info[DT_RUNPATH] == NULL on libleaf, so _dl_map_object walks up to main_map's DT_RPATH!
    c3 = tmp / "cell3"
    bin_dir, lib_main, lib_dep = build_base_tree(c3, leaf_uses_runpath=False)
    main3 = bin_dir / "main"
    subprocess.run(
        [
            "cc",
            str(src_dir / "main.c"),
            "-L",
            str(lib_main),
            "-lmid",
            f"-Wl,-rpath-link,{lib_main}:{lib_dep}",
            "-Wl,--disable-new-dtags",
            "-Wl,-rpath,$ORIGIN/../lib_main:$ORIGIN/../lib_dep",
            "-o",
            str(main3),
        ],
        check=True,
    )
    res3 = subprocess.run(["env", "-i", str(main3)], capture_output=True, text=True)
    cells.append(
        {
            "cell": "3_main_rpath_succeeds_when_leaf_has_no_runpath",
            "main_tags": read_dynamic_tags(main3),
            "leaf_tags": read_dynamic_tags(lib_main / "libleaf.so"),
            "exit_code": res3.returncode,
            "stdout": res3.stdout.strip(),
            "stderr_contains_libdep_missing": "libdep.so: cannot open shared object file" in res3.stderr,
        }
    )

    # Cell 4: Consumer-side patchelf --add-needed libdep.so on main_bin (with DT_RUNPATH).
    c4 = tmp / "cell4"
    bin_dir, lib_main, lib_dep = build_base_tree(c4, leaf_uses_runpath=True)
    main4 = bin_dir / "main"
    shutil.copy2(main1, main4)
    patchelf = shutil.which("patchelf") or str(
        sorted(Path("/nix/store").glob("*-patchelf-*/bin/patchelf"))[0]
    )
    subprocess.run([patchelf, "--add-needed", "libdep.so", str(main4)], check=True)
    res4 = subprocess.run(["env", "-i", str(main4)], capture_output=True, text=True)
    cells.append(
        {
            "cell": "4_consumer_add_needed_on_main",
            "main_tags": read_dynamic_tags(main4),
            "leaf_tags": read_dynamic_tags(lib_main / "libleaf.so"),
            "exit_code": res4.returncode,
            "stdout": res4.stdout.strip(),
            "stderr_contains_libdep_missing": "libdep.so: cannot open shared object file" in res4.stderr,
        }
    )

    # Cell 5: Producer-side co-location of libdep.so in lib_main/ (where libleaf's DT_RUNPATH=$ORIGIN points),
    # WITHOUT --add-needed on main_bin.
    c5 = tmp / "cell5"
    bin_dir, lib_main, lib_dep = build_base_tree(c5, leaf_uses_runpath=True)
    shutil.copy2(lib_dep / "libdep.so", lib_main / "libdep.so")
    main5 = bin_dir / "main"
    subprocess.run(
        [
            "cc",
            str(src_dir / "main.c"),
            "-L",
            str(lib_main),
            "-lmid",
            f"-Wl,-rpath-link,{lib_main}",
            "-Wl,--enable-new-dtags",
            "-Wl,-rpath,$ORIGIN/../lib_main",
            "-o",
            str(main5),
        ],
        check=True,
    )
    res5 = subprocess.run(["env", "-i", str(main5)], capture_output=True, text=True)
    cells.append(
        {
            "cell": "5_producer_colocation_in_leaf_runpath_without_add_needed",
            "main_tags": read_dynamic_tags(main5),
            "leaf_tags": read_dynamic_tags(lib_main / "libleaf.so"),
            "exit_code": res5.returncode,
            "stdout": res5.stdout.strip(),
            "stderr_contains_libdep_missing": "libdep.so: cannot open shared object file" in res5.stderr,
        }
    )

    return cells


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        while chunk := f.read(1 << 20):
            h.update(chunk)
    return h.hexdigest()


def probe_rust_toolchain_and_nix_lld(tmp: Path) -> dict:
    rust_stores = sorted(Path("/nix/store").glob("*-rust-toolchain-x86_64-linux-2026-05-31"))
    if not rust_stores:
        raise RuntimeError("Missing rust-toolchain-x86_64-linux-2026-05-31 in /nix/store")
    rust_store = rust_stores[0]

    glibc_store = sorted(Path("/nix/store").glob("*-glibc-2.42-*/lib/ld-linux-x86-64.so.2"))[0].parent.parent
    gcc_lib_store = sorted(Path("/nix/store").glob("*-gcc-15.2.0-lib/lib/libgcc_s.so.1"))[0].parent.parent
    zlib_store = sorted(Path("/nix/store").glob("*-zlib-1.3.*/lib/libz.so.1"))[0].parent.parent
    nix_cc = sorted(Path("/nix/store").glob("*-gcc-wrapper-15.2.0/bin/cc"))[0]
    binutils_bin = sorted(Path("/nix/store").glob("*-binutils-wrapper-*/bin/ld"))[0].parent
    coreutils_bin = sorted(Path("/nix/store").glob("*-coreutils-*/bin/env"))[0].parent

    # 1. Check duplicate libLLVM.so and librustc_driver.so between lib/ and lib/rustlib/x86_64-unknown-linux-gnu/lib/
    llvm_top = rust_store / "lib/libLLVM.so.22.1-rust-1.98.0-nightly"
    llvm_sub = rust_store / "lib/rustlib/x86_64-unknown-linux-gnu/lib/libLLVM.so.22.1-rust-1.98.0-nightly"
    drv_top = rust_store / "lib/librustc_driver-5d5a3c5207375ffc.so"
    drv_sub = rust_store / "lib/rustlib/x86_64-unknown-linux-gnu/lib/librustc_driver-5d5a3c5207375ffc.so"

    dup_info = {
        "libllvm_size_bytes": llvm_top.stat().st_size,
        "libllvm_top_sha256": sha256_file(llvm_top),
        "libllvm_rustlib_sha256": sha256_file(llvm_sub),
        "librustc_driver_size_bytes": drv_top.stat().st_size,
        "librustc_driver_top_sha256": sha256_file(drv_top),
        "librustc_driver_rustlib_sha256": sha256_file(drv_sub),
        "total_duplicate_bytes": llvm_top.stat().st_size + drv_top.stat().st_size,
    }

    # 2. Inspect ELF tags of rustc, librustc_driver, libLLVM, gcc-ld/ld.lld, and rust-lld
    elf_inventory = {
        "rustc": read_dynamic_tags(rust_store / "bin/rustc"),
        "librustc_driver": read_dynamic_tags(drv_top),
        "libLLVM": read_dynamic_tags(llvm_top),
        "gcc_ld_lld_wrapper": read_dynamic_tags(
            rust_store / "lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld/ld.lld"
        ),
        "rust_lld": read_dynamic_tags(
            rust_store / "lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld"
        ),
    }

    # 3. Test rustc 1.98 inside a Nix-like bwrap sandbox (no /lib64) with and without -Clinker-features=-lld
    build_dir = tmp / "nix_sandbox_build"
    build_dir.mkdir(parents=True, exist_ok=True)
    (build_dir / "hello.rs").write_text('fn main() { println!("sandbox_ok"); }\n')

    ld_linux = str(glibc_store / "lib/ld-linux-x86-64.so.2")
    lib_path = f"{rust_store}/lib:{gcc_lib_store}/lib:{glibc_store}/lib:{zlib_store}/lib"
    sandbox_path = f"{nix_cc.parent}:{binutils_bin}:{coreutils_bin}"

    def run_in_nix_sandbox(extra_rustc_args: list[str], out_name: str) -> subprocess.CompletedProcess:
        cmd = [
            "bwrap",
            "--tmpfs",
            "/",
            "--ro-bind",
            "/nix",
            "/nix",
            "--bind",
            str(build_dir),
            "/build",
            "--proc",
            "/proc",
            "--dev",
            "/dev",
            "--tmpfs",
            "/tmp",
            "--setenv",
            "PATH",
            sandbox_path,
            "--setenv",
            "TMPDIR",
            "/tmp",
            ld_linux,
            "--library-path",
            lib_path,
            str(rust_store / "bin/rustc"),
            "--sysroot",
            str(rust_store),
            f"-Clinker={nix_cc}",
            *extra_rustc_args,
            "/build/hello.rs",
            "-o",
            f"/build/{out_name}",
        ]
        return subprocess.run(cmd, capture_output=True, text=True)

    res_default_lld = run_in_nix_sandbox([], "hello_default")
    res_disable_lld = run_in_nix_sandbox(["-Clinker-features=-lld"], "hello_nolld")
    run_out = subprocess.run([str(build_dir / "hello_nolld")], capture_output=True, text=True)

    return {
        "duplicate_shared_objects": dup_info,
        "upstream_rust_elf_tags": elf_inventory,
        "nix_sandbox_rustc_1_98_lld_probe": {
            "default_lld_enabled": {
                "exit_code": res_default_lld.returncode,
                "contains_gcc_ld_B_flag": "-B" in res_default_lld.stderr and "gcc-ld" in res_default_lld.stderr,
                "contains_fuse_ld_lld": "-fuse-ld=lld" in res_default_lld.stderr,
                "contains_collect2_posix_spawnp_enoent": "collect2: fatal error: posix_spawnp: No such file or directory"
                in res_default_lld.stderr,
            },
            "with_linker_features_minus_lld": {
                "exit_code": res_disable_lld.returncode,
                "compiled_binary_stdout": run_out.stdout.strip(),
            },
        },
    }


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="anneal-elf-lld-probe-") as tmp:
        tmp_path = Path(tmp)
        synthetic_cells = run_synthetic_five_cell_matrix(tmp_path)
        rust_nix_lld = probe_rust_toolchain_and_nix_lld(tmp_path)

    payload = {
        "synthetic_five_cell_dl_load_matrix": synthetic_cells,
        "rust_toolchain_and_nix_lld": rust_nix_lld,
    }
    (HERE / "results.json").write_text(json.dumps(payload, indent=2) + "\n")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
