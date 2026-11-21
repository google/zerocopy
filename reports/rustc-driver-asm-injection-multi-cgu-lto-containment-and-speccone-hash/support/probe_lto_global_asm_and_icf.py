#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone probe for ThinLTO / FatLTO `IRMover` `GlobalScopeAsm` cross-crate containment,
`.anneal.asm_sites` (`SHF_EXCLUDE`) survival across `.lto.rcgu.o`, and `rust-lld` / `ld.bfd`
`--icf={none,safe,all}` function-folding and FDE/site attribution."""

from __future__ import annotations

import argparse
import glob
import json
import os
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any

from probe_driver_cgu_and_invariance import (
    SHF_EXCLUDE,
    build_driver,
    extract_attested_sites,
    parse_elf64_reloc,
)

SHT_LLVM_ADDRSIG = 0x6FFF4C03
STT_GNU_IFUNC = 10
STB_WEAK = 2


def count_eh_frame_fdes(elf_path: str | Path) -> int:
    elf = parse_elf64_reloc(elf_path)
    sec = [s for s in elf["shdrs"] if s["name"] == ".eh_frame"]
    if not sec:
        return 0
    data = sec[0]["data"]
    pos = 0
    fdes = 0
    while pos + 4 <= len(data):
        length = struct.unpack_from("<I", data, pos)[0]
        pos += 4
        if length == 0:
            continue
        if length == 0xFFFFFFFF:
            if pos + 8 > len(data):
                break
            length = struct.unpack_from("<Q", data, pos)[0]
            pos += 8
        if pos + 4 > len(data):
            break
        cie_id = struct.unpack_from("<I", data, pos)[0]
        if cie_id != 0:
            fdes += 1
        pos += length
    return fdes


def build_upstream_and_sibling(drv_bin: Path, sysroot: str, work: Path) -> tuple[Path, Path]:
    up_src = work / "upstream_safe.rs"
    up_src.write_text(
        """#[no_mangle]
#[inline(never)]
pub extern "C" fn upstream_pure_auth() -> u64 {
    std::hint::black_box(1)
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn upstream_pure_ifunc_target() -> usize {
    std::hint::black_box(42)
}

#[inline(never)]
pub fn upstream_pure_catch_unwind() -> bool {
    std::panic::catch_unwind(|| {
        panic!("expected unwind");
    })
    .is_err()
}

#[inline(never)]
pub unsafe fn upstream_asm_sub_never_inline(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "sub {0:r}, {1:r}",
        inout(reg) a,
        in(reg) b,
        options(pure, nomem, nostack),
    );
    a
}

pub unsafe fn upstream_asm_sub_thinlto_importable(mut a: u64, b: u64) -> u64 {
    // Non-leaf (`calls > 0`) so MIR `cross_crate_inlinable` is false, leaving cross-crate
    // importing strictly to LLVM ThinLTO / FatLTO!
    let k = upstream_pure_auth().wrapping_sub(1);
    core::arch::asm!(
        "sub {0:r}, {1:r}",
        inout(reg) a,
        in(reg) b.wrapping_add(k),
        options(pure, nomem, nostack),
    );
    a
}
"""
    )
    up_rlib = work / "libupstream_safe.rlib"
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    env["ANNEAL_SYSROOT"] = sysroot
    env["ANNEAL_ASM_WRAP_MODE"] = "cr_zero_drift"
    env["ANNEAL_SESSION_NONCE"] = "aaaa1111bbbb2222cccc3333dddd4444"
    subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-name=upstream_safe",
            "--crate-type=rlib",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=1",
            str(up_src),
            "-o",
            str(up_rlib),
        ],
        env=env,
        check=True,
        capture_output=True,
        text=True,
    )

    # Also build a sibling `.rlib` (`z_sibling_dep`, alphabetically after `upstream_safe` in
    # `rustc_codegen_llvm/src/back/lto.rs:301` `serialized_modules.sort_by`) containing both
    # `global_asm!(".macro sub ...")` and an uncalled `asm!(".weak upstream_pure_auth")`!
    sib_src = work / "z_sibling_dep.rs"
    sib_src.write_text(
        """core::arch::global_asm!(".macro sub dst, src\\nadd \\\\dst, \\\\src\\n.endm");
#[inline(never)]
pub fn sibling_touch() -> u64 { std::hint::black_box(0) }
#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn z_uncalled_weak_downgrade() {
    core::arch::asm!(".weak upstream_pure_auth", options(nomem, nostack));
}
"""
    )
    sib_rlib = work / "libz_sibling_dep.rlib"
    env_sib = env.copy()
    env_sib["ANNEAL_ASM_WRAP_MODE"] = "off"
    subprocess.run(
        [
            str(drv_bin),
            "--edition=2021",
            "--crate-name=z_sibling_dep",
            "--crate-type=rlib",
            "-C",
            "opt-level=3",
            "-C",
            "codegen-units=1",
            str(sib_src),
            "-o",
            str(sib_rlib),
        ],
        env=env_sib,
        check=True,
        capture_output=True,
        text=True,
    )
    return up_rlib, sib_rlib


def test_lto_global_asm_matrix(
    drv_bin: Path, sysroot: str, work: Path
) -> dict[str, Any]:
    up_rlib, sib_rlib = build_upstream_and_sibling(drv_bin, sysroot, work)
    lto_modes = ["off", "thin", "fat"]
    cgu_counts = [1, 16]
    matrix: dict[str, Any] = {}

    env_base = os.environ.copy()
    env_base["RUSTC_BOOTSTRAP"] = "1"
    env_base["ANNEAL_SYSROOT"] = sysroot
    env_base["ANNEAL_ASM_WRAP_MODE"] = "cr_zero_drift"
    env_base["ANNEAL_SESSION_NONCE"] = "eeee5555ffff66660000777711118888"

    for lto in lto_modes:
        for cgu in cgu_counts:
            cell_key = f"lto_{lto}_cgu_{cgu}"
            cell_dir = work / cell_key
            cell_dir.mkdir(exist_ok=True)

            # Vector 1: Downstream `global_asm!(".macro sub ...")` vs upstream `#[inline(never)]`
            # and ThinLTO-importable `asm!` functions, PLUS `.anneal.asm_sites` survival in `.rcgu.o`!
            v1_dir = cell_dir / "v1_macro"
            v1_dir.mkdir(exist_ok=True)
            v1_src = v1_dir / "main.rs"
            v1_src.write_text(
                """extern crate upstream_safe;
core::arch::global_asm!(".macro sub dst, src\\nadd \\\\dst, \\\\src\\n.endm");
fn main() {
    unsafe {
        let r_never = upstream_safe::upstream_asm_sub_never_inline(20, 5);
        let r_imp = upstream_safe::upstream_asm_sub_thinlto_importable(20, 5);
        println!("{r_never},{r_imp}");
    }
}
"""
            )
            p1 = subprocess.run(
                [
                    str(drv_bin),
                    "--edition=2021",
                    "--crate-type=bin",
                    "-C",
                    "opt-level=3",
                    "-C",
                    f"lto={lto}",
                    "-C",
                    f"codegen-units={cgu}",
                    "-C",
                    "save-temps",
                    str(v1_src),
                    "--extern",
                    f"upstream_safe={up_rlib}",
                    "--out-dir",
                    str(v1_dir),
                ],
                env=env_base,
                capture_output=True,
                text=True,
            )
            r_never, r_imp = -1, -1
            v1_sites = []
            has_add_opcode_in_site = False
            if p1.returncode == 0:
                out1 = subprocess.check_output([str(v1_dir / "main")], text=True).strip()
                r_never, r_imp = [int(x) for x in out1.split(",")]
                for o in sorted(glob.glob(str(v1_dir / "*.o"))):
                    if o.endswith(".rcgu.o"):
                        v1_sites.extend(extract_attested_sites(o))
                # `48 01 ...` is 64-bit ADD (`0x01`), whereas `48 29 ...` is 64-bit SUB (`0x29`).
                has_add_opcode_in_site = any(
                    len(s["slice_hex"]) >= 4 and s["slice_hex"][2:4] == "01" for s in v1_sites
                )

            # Vector 1b: Sibling `.rlib` `global_asm!(".macro sub ...")` (downstream has ZERO asm!)
            v1b_dir = cell_dir / "v1b_sibling"
            v1b_dir.mkdir(exist_ok=True)
            v1b_src = v1b_dir / "main.rs"
            v1b_src.write_text(
                """extern crate upstream_safe;
extern crate z_sibling_dep;
fn main() {
    unsafe {
        let z = z_sibling_dep::sibling_touch();
        let r_never = upstream_safe::upstream_asm_sub_never_inline(20, 5).wrapping_add(z);
        println!("{r_never}");
    }
}
"""
            )
            subprocess.run(
                [
                    str(drv_bin),
                    "--edition=2021",
                    "--crate-type=bin",
                    "-C",
                    "opt-level=3",
                    "-C",
                    f"lto={lto}",
                    "-C",
                    f"codegen-units={cgu}",
                    str(v1b_src),
                    "--extern",
                    f"upstream_safe={up_rlib}",
                    "--extern",
                    f"z_sibling_dep={sib_rlib}",
                    "--out-dir",
                    str(v1b_dir),
                ],
                env=env_base,
                check=True,
                capture_output=True,
                text=True,
            )
            sib_r_never = int(subprocess.check_output([str(v1b_dir / "main")], text=True).strip())

            # Vector 2: `.type upstream_pure_ifunc_target, @gnu_indirect_function` in downstream `global_asm!`
            v2_dir = cell_dir / "v2_ifunc"
            v2_dir.mkdir(exist_ok=True)
            v2_src = v2_dir / "main.rs"
            v2_src.write_text(
                """extern crate upstream_safe;
core::arch::global_asm!(".type upstream_pure_ifunc_target, @gnu_indirect_function");
fn main() {
    let f: extern "C" fn() -> usize = upstream_safe::upstream_pure_ifunc_target;
    std::hint::black_box(f as usize);
}
"""
            )
            p2 = subprocess.run(
                [
                    str(drv_bin),
                    "--edition=2021",
                    "--crate-type=bin",
                    "-C",
                    "opt-level=3",
                    "-C",
                    f"lto={lto}",
                    "-C",
                    f"codegen-units={cgu}",
                    str(v2_src),
                    "--extern",
                    f"upstream_safe={up_rlib}",
                    "--out-dir",
                    str(v2_dir),
                ],
                env=env_base,
                capture_output=True,
                text=True,
            )
            promoted_to_ifunc = False
            if p2.returncode == 0:
                v2_elf = parse_elf64_reloc(v2_dir / "main")
                ifunc_syms = [
                    s["type"]
                    for s in v2_elf["syms"]
                    if s["name"] == "upstream_pure_ifunc_target" and s["shndx"] != 0
                ]
                promoted_to_ifunc = STT_GNU_IFUNC in ifunc_syms

            # Vector 3: Uncalled `.weak upstream_pure_auth` + C/asm strong override across crates
            v3_dir = cell_dir / "v3_weak"
            v3_dir.mkdir(exist_ok=True)
            c_override = v3_dir / "override.o"
            s_override = v3_dir / "override.s"
            s_override.write_text(
                """.text
.globl upstream_pure_auth
.type upstream_pure_auth, @function
upstream_pure_auth:
    movq $999, %rax
    retq
"""
            )
            subprocess.run(["llvm-mc", "-filetype=obj", str(s_override), "-o", str(c_override)], check=True)
            v3_src = v3_dir / "main.rs"
            v3_src.write_text(
                """extern crate upstream_safe;
extern crate z_sibling_dep;
fn main() {
    std::hint::black_box(z_sibling_dep::z_uncalled_weak_downgrade as usize);
    println!("{}", upstream_safe::upstream_pure_auth());
}
"""
            )
            env_v3 = env_base.copy()
            env_v3["ANNEAL_ASM_WRAP_MODE"] = "off"
            p3 = subprocess.run(
                [
                    str(drv_bin),
                    "--edition=2021",
                    "--crate-type=bin",
                    "-C",
                    "opt-level=3",
                    "-C",
                    f"lto={lto}",
                    "-C",
                    f"codegen-units={cgu}",
                    f"-Clink-arg={c_override}",
                    str(v3_src),
                    "--extern",
                    f"upstream_safe={up_rlib}",
                    "--extern",
                    f"z_sibling_dep={sib_rlib}",
                    "--out-dir",
                    str(v3_dir),
                ],
                env=env_v3,
                capture_output=True,
                text=True,
            )
            weak_override_val = None
            if p3.returncode == 0:
                weak_override_val = int(
                    subprocess.check_output([str(v3_dir / "main")], text=True).strip()
                )

            # Vector 4: `global_asm!(".cfi_sections .debug_frame")` vs upstream `catch_unwind`
            v4_dir = cell_dir / "v4_cfi"
            v4_dir.mkdir(exist_ok=True)
            v4_src = v4_dir / "main.rs"
            v4_src.write_text(
                """extern crate upstream_safe;
core::arch::global_asm!(".cfi_sections .debug_frame");
fn main() {
    assert!(upstream_safe::upstream_pure_catch_unwind());
}
"""
            )
            subprocess.run(
                [
                    str(drv_bin),
                    "--edition=2021",
                    "--crate-type=bin",
                    "-C",
                    "opt-level=3",
                    "-C",
                    f"lto={lto}",
                    "-C",
                    f"codegen-units={cgu}",
                    str(v4_src),
                    "--extern",
                    f"upstream_safe={up_rlib}",
                    "--out-dir",
                    str(v4_dir),
                ],
                env=env_base,
                check=True,
                capture_output=True,
                text=True,
            )
            r4 = subprocess.run([str(v4_dir / "main")], capture_output=True, text=True)

            matrix[cell_key] = {
                "downstream_macro_vs_upstream_never_inline": r_never,
                "downstream_macro_vs_upstream_thinlto_importable": r_imp,
                "sibling_rlib_macro_vs_upstream_never_inline": sib_r_never,
                "lto_rcgu_attested_sites_count": len(v1_sites),
                "lto_rcgu_detected_add_opcode": has_add_opcode_in_site,
                "upstream_pure_promoted_to_ifunc": promoted_to_ifunc,
                "weak_override_link_rc": p3.returncode,
                "weak_override_runtime_val": weak_override_val,
                "cfi_strip_upstream_catch_unwind_rc": r4.returncode,
            }

    return matrix


def test_icf_matrix(drv_bin: Path, sysroot: str, work: Path) -> dict[str, Any]:
    icf_src = work / "icf_test.rs"
    icf_src.write_text(
        """#[unsafe(naked)]
pub unsafe extern "C" fn naked_twin_a(x: u64) -> u64 {
    core::arch::naked_asm!(
        "lea rax, [rdi + 42]",
        "ret",
    )
}

#[unsafe(naked)]
pub unsafe extern "C" fn naked_twin_b(x: u64) -> u64 {
    core::arch::naked_asm!(
        "lea rax, [rdi + 42]",
        "ret",
    )
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn asm_twin_a(mut x: u64) -> u64 {
    core::arch::asm!(
        "add {0:r}, 42",
        inout(reg) x,
        options(pure, nomem, nostack),
    );
    x
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn asm_twin_b(mut x: u64) -> u64 {
    core::arch::asm!(
        "add {0:r}, 42",
        inout(reg) x,
        options(pure, nomem, nostack),
    );
    x
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn pure_twin_a(x: u64) -> u64 {
    x.wrapping_mul(3).wrapping_add(7)
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn pure_twin_b(x: u64) -> u64 {
    x.wrapping_mul(3).wrapping_add(7)
}

fn main() {
    let na = naked_twin_a as *const () as usize;
    let nb = naked_twin_b as *const () as usize;
    let aa = asm_twin_a as *const () as usize;
    let ab = asm_twin_b as *const () as usize;
    let pa = pure_twin_a as *const () as usize;
    let pb = pure_twin_b as *const () as usize;
    unsafe {
        let sum = naked_twin_a(1) + naked_twin_b(1) + asm_twin_a(1) + asm_twin_b(1)
            + pure_twin_a(1) + pure_twin_b(1);
        std::hint::black_box(sum);
    }
    println!(
        "{},{},{}",
        int_bool(na == nb),
        int_bool(aa == ab),
        int_bool(pa == pb)
    );
}

fn int_bool(b: bool) -> u8 {
    if b { 1 } else { 0 }
}
"""
    )

    lld_dir = Path(sysroot) / "lib/rustlib/x86_64-unknown-linux-gnu/bin/gcc-ld"
    env_base = os.environ.copy()
    env_base["RUSTC_BOOTSTRAP"] = "1"
    env_base["ANNEAL_SYSROOT"] = sysroot
    env_base["ANNEAL_ASM_WRAP_MODE"] = "cr_zero_drift"
    env_base["ANNEAL_SESSION_NONCE"] = "99998888777766665555444433332222"

    results: dict[str, Any] = {"rust_lld": {}, "ld_bfd": {}}

    for lto in ["off", "thin", "fat"]:
        for cgu in [1, 16]:
            for icf in ["none", "safe", "all"]:
                for addrsig in [False, True]:
                    # Only expand addrsig=True on cgu=1 lto=off to keep matrix fast while proving
                    # the exact `SHT_LLVM_ADDRSIG` mechanism in `lld/ELF/Driver.cpp:2730-2750`!
                    if addrsig and not (lto == "off" and cgu == 1):
                        continue
                    key = f"lto_{lto}_cgu_{cgu}_icf_{icf}" + ("_addrsig" if addrsig else "")
                    out_d = work / f"lld_{key}"
                    out_d.mkdir(exist_ok=True)
                    extra = ["-C", "llvm-args=-addrsig"] if addrsig else []
                    proc = subprocess.run(
                        [
                            str(drv_bin),
                            "--edition=2021",
                            "--crate-type=bin",
                            "-C",
                            "opt-level=3",
                            "-C",
                            f"lto={lto}",
                            "-C",
                            f"codegen-units={cgu}",
                            "-C",
                            "save-temps",
                            f"-Clink-arg=-B{lld_dir}",
                            "-Clink-arg=-fuse-ld=lld",
                            f"-Clink-arg=-Wl,--icf={icf}",
                            *extra,
                            str(icf_src),
                            "--out-dir",
                            str(out_d),
                        ],
                        env=env_base,
                        capture_output=True,
                        text=True,
                    )
                    if proc.returncode != 0:
                        raise RuntimeError(f"lld {key} failed:\n{proc.stderr}")

                    rt = subprocess.check_output([str(out_d / "icf_test")], text=True).strip()
                    naked_eq, asm_eq, pure_eq = [x == "1" for x in rt.split(",")]

                    rcgu_objs = [
                        o for o in sorted(glob.glob(str(out_d / "*.o"))) if o.endswith(".rcgu.o")
                    ]
                    has_addrsig_sec = False
                    prelink_sites = 0
                    for o in rcgu_objs:
                        eo = parse_elf64_reloc(o)
                        if any(s["type"] == SHT_LLVM_ADDRSIG for s in eo["shdrs"]):
                            has_addrsig_sec = True
                        prelink_sites += len(extract_attested_sites(o))

                    bin_elf = parse_elf64_reloc(out_d / "icf_test")
                    fdes = count_eh_frame_fdes(out_d / "icf_test")
                    sym_addrs = {
                        s["name"]: s["value"]
                        for s in bin_elf["syms"]
                        if any(
                            k in s["name"]
                            for k in [
                                "naked_twin_a",
                                "naked_twin_b",
                                "asm_twin_a",
                                "asm_twin_b",
                                "pure_twin_a",
                                "pure_twin_b",
                            ]
                        )
                    }
                    results["rust_lld"][key] = {
                        "has_llvm_addrsig_section": has_addrsig_sec,
                        "prelink_attested_sites": prelink_sites,
                        "naked_folded": naked_eq,
                        "asm_folded": asm_eq,
                        "pure_folded": pure_eq,
                        "eh_frame_fde_count": fdes,
                        "distinct_twin_addresses": len(set(sym_addrs.values())),
                    }

    # Also probe GNU `ld.bfd 2.47` on `--icf=none` / `--icf=safe` / `--icf=all`:
    for icf in ["none", "safe", "all"]:
        bfd_d = work / f"bfd_{icf}"
        bfd_d.mkdir(exist_ok=True)
        p_bfd = subprocess.run(
            [
                str(drv_bin),
                "--edition=2021",
                "--crate-type=bin",
                "-C",
                "opt-level=3",
                "-Clink-arg=-fuse-ld=bfd",
                f"-Clink-arg=-Wl,--icf={icf}",
                str(icf_src),
                "--out-dir",
                str(bfd_d),
            ],
            env=env_base,
            capture_output=True,
            text=True,
        )
        results["ld_bfd"][f"icf_{icf}"] = {
            "rc": p_bfd.returncode,
            "unsupported_flag": ("unrecognized option" in p_bfd.stderr or p_bfd.returncode != 0),
            "stderr_first_line": p_bfd.stderr.strip().splitlines()[0] if p_bfd.stderr.strip() else "",
        }

    return results


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchains", nargs="+", default=["1.99.1", "nightly"])
    parser.add_argument("--out", type=str, default="")
    args = parser.parse_args()

    here = Path(__file__).resolve().parent
    driver_src = here / "anneal_driver_prototype.rs"

    out_data: dict[str, Any] = {"toolchains": {}}
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp)
        for tc in args.toolchains:
            tc_w = work / tc.replace("/", "_")
            tc_w.mkdir(exist_ok=True)
            drv_bin, sysroot = build_driver(tc, driver_src, tc_w)
            ver = (
                subprocess.check_output(["rustup", "run", tc, "rustc", "-vV"], text=True)
                .strip()
                .splitlines()[0]
            )
            out_data["toolchains"][tc] = {
                "rustc_version": ver,
                "lto_global_asm_matrix": test_lto_global_asm_matrix(drv_bin, sysroot, tc_w),
                "icf_matrix": test_icf_matrix(drv_bin, sysroot, tc_w),
            }

    out_json = json.dumps(out_data, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(out_json)
    print(out_json)


if __name__ == "__main__":
    main()
