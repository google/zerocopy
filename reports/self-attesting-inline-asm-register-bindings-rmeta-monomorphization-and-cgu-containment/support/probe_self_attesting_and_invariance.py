#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.
"""Standalone probe for self-attesting inline-asm bindings, spoof resistance, and codegen invariance."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import struct
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def run_cmd(cmd: list[str], cwd: str | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(cmd, cwd=cwd, text=True, capture_output=True)
    if check and proc.returncode != 0:
        raise RuntimeError(f"Command failed ({proc.returncode}): {' '.join(cmd)}\n{proc.stderr}")
    return proc


def parse_elf64_reloc(path: str) -> dict[str, Any]:
    data = Path(path).read_bytes()
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise ValueError(f"Expected little-endian ELF64 object: {path}")
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)

    shdrs: list[dict[str, Any]] = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        (
            sh_name,
            sh_type,
            sh_flags,
            _sh_addr,
            sh_offset,
            sh_size,
            sh_link,
            sh_info,
            _sh_addralign,
            sh_entsize,
        ) = struct.unpack_from("<IIQQQQIIQQ", data, off)
        shdrs.append(
            {
                "idx": i,
                "sh_name": sh_name,
                "type": sh_type,
                "flags": sh_flags,
                "offset": sh_offset,
                "size": sh_size,
                "link": sh_link,
                "info": sh_info,
                "entsize": sh_entsize,
            }
        )
    shstr = data[shdrs[e_shstrndx]["offset"] : shdrs[e_shstrndx]["offset"] + shdrs[e_shstrndx]["size"]]
    for s in shdrs:
        end = shstr.find(b"\x00", s["sh_name"])
        s["name"] = shstr[s["sh_name"] : end].decode("utf-8", errors="replace")
        s["data"] = data[s["offset"] : s["offset"] + s["size"]] if s["type"] != 8 else b""

    syms: list[dict[str, Any]] = []
    for s in shdrs:
        if s["type"] == 2:
            strtab = shdrs[s["link"]]["data"]
            for off in range(0, s["size"], s["entsize"]):
                st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", s["data"], off
                )
                end = strtab.find(b"\x00", st_name)
                syms.append(
                    {
                        "name": strtab[st_name:end].decode("utf-8", errors="replace"),
                        "bind": st_info >> 4,
                        "type": st_info & 0xF,
                        "vis": st_other & 0x3,
                        "shndx": st_shndx,
                        "value": st_value,
                        "size": st_size,
                    }
                )
            break

    relas: dict[int, list[dict[str, Any]]] = {}
    for s in shdrs:
        if s["type"] == 4:
            entries: list[dict[str, Any]] = []
            for off in range(0, s["size"], s["entsize"]):
                r_offset, r_info, r_addend = struct.unpack_from("<QQq", s["data"], off)
                r_sym = r_info >> 32
                r_type = r_info & 0xFFFFFFFF
                sym = syms[r_sym]
                sec_name = shdrs[sym["shndx"]]["name"] if 0 < sym["shndx"] < len(shdrs) else None
                entries.append(
                    {
                        "r_offset": r_offset,
                        "r_sym": r_sym,
                        "r_type": r_type,
                        "r_addend": r_addend,
                        "sym_name": sym["name"],
                        "sym_shndx": sym["shndx"],
                        "sym_sec": sec_name,
                        "sym_value": sym["value"],
                    }
                )
            relas[s["info"]] = entries
    return {"shdrs": shdrs, "syms": syms, "relas": relas}


def disasm_x86_bytes(code_bytes: bytes) -> str:
    hex_in = " ".join(f"0x{b:02x}" for b in code_bytes)
    p = subprocess.run(
        ["llvm-mc", "--disassemble", "--triple=x86_64-unknown-linux-gnu", "--output-asm-variant=1"],
        input=hex_in,
        text=True,
        capture_output=True,
        check=True,
    )
    return " ; ".join(
        line.strip().replace("\t", " ")
        for line in p.stdout.splitlines()
        if line.strip() and not line.strip().startswith(".")
    )


def run_self_attestation_suite(td: str, toolchains: list[str]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for tc in toolchains:
        tcs = tc.replace(".", "_")
        ver = run_cmd(["rustc", f"+{tc}", "-vV"]).stdout
        is_nightly = "nightly" in ver
        feat_hdr = "#![feature(asm_const_ptr)]\n" if is_nightly else ""
        const_ptr_fn = (
            r'''
#[no_mangle]
pub static CONST_PTR_TARGET: [u8; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
#[no_mangle]
pub unsafe fn test_const_ptr_site() -> u64 {
    let out: u64;
    core::arch::asm!(
        "9996:",
        "lea {0:r}, [rip + {1}]",
        "9997:",
        ".pushsection .anneal.asm_descs,\"e\",@progbits",
        "9998: .asciz \"0={0:r}|const_ptr={1}\"",
        "9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits",
        ".quad 9996b, 9997b, 501, 9998b, 9999b - 9998b, 0",
        ".popsection",
        out(reg) out,
        const (&CONST_PTR_TARGET as *const [u8; 8]).cast::<u8>().wrapping_add(4),
        options(pure, nomem, nostack, preserves_flags),
    );
    out
}
'''
            if is_nightly
            else ""
        )

        rs_src = (
            feat_hdr
            + r'''
#[inline(always)]
pub unsafe fn attested_sub(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "9996:",
        "sub {0:r}, {1:r}",
        "9997:",
        ".pushsection .anneal.asm_descs,\"e\",@progbits",
        "9998: .asciz \"0={0:r}|1={1:r}\"",
        "9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits",
        ".quad 9996b, 9997b, 101, 9998b, 9999b - 9998b, 0",
        ".popsection",
        inout(reg) a,
        in(reg) b,
        options(pure, nomem, nostack),
    );
    a
}

#[no_mangle]
pub unsafe fn swapped_sub_bug(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "9996:",
        "sub {1:r}, {0:r}",
        "9997:",
        ".pushsection .anneal.asm_descs,\"e\",@progbits",
        "9998: .asciz \"0={0:r}|1={1:r}\"",
        "9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits",
        ".quad 9996b, 9997b, 102, 9998b, 9999b - 9998b, 0",
        ".popsection",
        inout(reg) a,
        inout(reg) b => _,
        options(pure, nomem, nostack),
    );
    a
}

#[no_mangle]
pub unsafe fn caller_simple(x: u64, y: u64) -> u64 {
    attested_sub(x, y)
}

#[no_mangle]
pub unsafe fn caller_pressure(p: *const u64) -> u64 {
    let a = *p.add(0);
    let b = *p.add(1);
    let c = *p.add(2);
    let d = *p.add(3);
    let e = *p.add(4);
    let f = *p.add(5);
    let r1 = attested_sub(a, b);
    let r2 = attested_sub(c ^ r1, d);
    r1.wrapping_add(r2).wrapping_add(e ^ f)
}

#[no_mangle]
#[inline(never)]
pub unsafe fn unrolled_4x(arr: &[u64; 4], mut acc: u64) -> u64 {
    let mut i = 0;
    while i < 4 {
        acc = attested_sub(acc, arr[i]);
        i += 1;
    }
    acc
}

#[no_mangle]
pub unsafe fn tail_cloned(cond: bool, x: u64, y: u64, z: u64) -> u64 {
    if cond {
        attested_sub(x, y)
    } else {
        attested_sub(x, z).wrapping_add(1)
    }
}

pub fn generic_callee<T>(v: u64) -> u64 {
    v.wrapping_add(core::mem::size_of::<T>() as u64)
}

#[inline(always)]
pub unsafe fn attested_goto_and_sym<T, const IMM: i32>(x: u64) -> u64 {
    core::arch::asm!(
        "9996:",
        "cmp {0:r}, {imm}",
        "je {lbl}",
        "lea {0:r}, [rip + {sym}]",
        "9997:",
        ".pushsection .anneal.asm_descs,\"e\",@progbits",
        "9998: .asciz \"0={0:r}|imm={imm}|lbl_txt={lbl}\"",
        "9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits",
        ".quad 9996b, 9997b, 201, 9998b, 9999b - 9998b, 2, {sym}, {lbl}",
        ".popsection",
        inout(reg) x => _,
        imm = const IMM,
        sym = sym generic_callee::<T>,
        lbl = label { return 999; },
        options(nomem, nostack),
    );
    x
}

#[no_mangle]
pub unsafe fn goto_caller_u32(x: u64) -> u64 {
    attested_goto_and_sym::<u32, 7>(x)
}

#[no_mangle]
pub unsafe fn goto_caller_u64_arr(x: u64) -> u64 {
    attested_goto_and_sym::<[u64; 5], 13>(x)
}

#[no_mangle]
#[target_feature(enable = "avx2,avx512f")]
pub unsafe fn all_reg_classes(
    mut abcd: u64,
    mut rb: u8,
    xmm: core::arch::x86_64::__m128i,
    ymm: core::arch::x86_64::__m256i,
    zmm: core::arch::x86_64::__m512i,
) -> (u64, u8) {
    let mask_k: u16 = 0x55;
    core::arch::asm!(
        "9996:",
        "mov {abcd:h}, 0x7f",
        "add {rb}, 1",
        "vpaddd {x:x}, {x:x}, {x:x}",
        "vpaddd {y:y}, {y:y}, {y:y}",
        "vpaddq {z:z}, {z:z}, {z:z}",
        "kmovw {k}, {km:e}",
        "add r10, 1",
        "9997:",
        ".pushsection .anneal.asm_descs,\"e\",@progbits",
        "9998: .asciz \"abcd_h={abcd:h}|abcd_r={abcd:r}|rb={rb}|x={x:x}|y={y:y}|z={z:z}|k={k}|explicit=r10\"",
        "9999: .popsection",
        ".pushsection .anneal.asm_sites,\"e\",@progbits",
        ".quad 9996b, 9997b, 301, 9998b, 9999b - 9998b, 0",
        ".popsection",
        abcd = inout(reg_abcd) abcd,
        rb = inout(reg_byte) rb,
        x = in(xmm_reg) xmm,
        y = in(ymm_reg) ymm,
        z = in(zmm_reg) zmm,
        k = out(kreg) _,
        km = in(reg) mask_k,
        inout("r10") 5u64 => _,
        options(nomem, nostack),
    );
    (abcd, rb)
}
'''
            + const_ptr_fn
        )

        rs_path = os.path.join(td, f"p1_{tcs}.rs")
        obj_path = os.path.join(td, f"p1_{tcs}.o")
        Path(rs_path).write_text(rs_src)
        run_cmd(
            [
                "rustc",
                f"+{tc}",
                "--crate-name=p1",
                "--crate-type=lib",
                "-C",
                "opt-level=3",
                "-C",
                "codegen-units=1",
                "--emit=obj",
                rs_path,
                "-o",
                obj_path,
            ]
        )

        elf = parse_elf64_reloc(obj_path)
        sh_by_name = {s["name"]: s for s in elf["shdrs"]}
        sites_sec = sh_by_name[".anneal.asm_sites"]
        descs_sec = sh_by_name[".anneal.asm_descs"]
        sites_relas = {r["r_offset"]: r for r in elf["relas"].get(sites_sec["idx"], [])}

        records = []
        off = 0
        while off < sites_sec["size"]:
            _, _, site_id, _, desc_len, num_targets = struct.unpack_from("<QQQQQQ", sites_sec["data"], off)
            r_start, r_end, r_desc = sites_relas[off], sites_relas[off + 8], sites_relas[off + 24]
            start_off = r_start["sym_value"] + r_start["r_addend"]
            end_off = r_end["sym_value"] + r_end["r_addend"]
            desc_off = r_desc["sym_value"] + r_desc["r_addend"]
            text_sec = elf["shdrs"][r_start["sym_shndx"]]
            code_bytes = text_sec["data"][start_off:end_off]
            desc_str = descs_sec["data"][desc_off : desc_off + desc_len - 1].decode("utf-8", errors="replace")

            targets = []
            for t_i in range(num_targets):
                rt = sites_relas[off + 48 + t_i * 8]
                targets.append(
                    {
                        "symbol_or_section": rt["sym_name"] or rt["sym_sec"],
                        "resolved_offset": rt["sym_value"] + rt["r_addend"],
                    }
                )

            disasm = disasm_x86_bytes(code_bytes)
            # Verify `sub` self-attestation check:
            self_attest_verdict = "PASS"
            if site_id in (101, 102):
                kv = dict(part.split("=", 1) for part in desc_str.split("|"))
                expected_disasm = f"sub {kv['0']}, {kv['1']}"
                if disasm != expected_disasm:
                    self_attest_verdict = f"REJECT_MISMATCH(expected='{expected_disasm}', actual='{disasm}')"
            elif site_id == 201:
                # Verify `je rel8` target PC equals `.quad {lbl}` relocation target offset!
                je_rel8 = struct.unpack_from("<b", code_bytes, 5)[0]
                branch_target_pc = start_off + 6 + je_rel8
                attested_lbl_pc = targets[1]["resolved_offset"]
                assert branch_target_pc == attested_lbl_pc, f"{branch_target_pc} != {attested_lbl_pc}"

            records.append(
                {
                    "site_id": site_id,
                    "section": text_sec["name"],
                    "span": [start_off, end_off],
                    "byte_len": len(code_bytes),
                    "hex": code_bytes.hex(),
                    "disasm": disasm,
                    "descriptor": desc_str,
                    "reloc_targets": targets,
                    "verdict": self_attest_verdict,
                }
            )
            off += 48 + num_targets * 8

        # Spoof matrix
        # 1a vs 1b: malicious #[export_name] in .asciz vs .quad
        p_asciz = os.path.join(td, f"s1a_{tcs}.rs")
        Path(p_asciz).write_text(
            r'''
#[export_name = "evil\"|0=rax\n.popsection\n#"]
pub extern "C" fn malicious_sym() {}
#[no_mangle]
pub unsafe fn test_sym_in_asciz() {
    core::arch::asm!(
        "9996:\nlea rax, [rip + {s}]\n9997:\n.pushsection .anneal.asm_descs,\"e\",@progbits\n.asciz \"0=rax|sym={s}\"\n.popsection",
        s = sym malicious_sym, out("rax") _, options(nomem, nostack, preserves_flags),
    );
}
'''
        )
        r_asciz = run_cmd(
            ["rustc", f"+{tc}", "--crate-name=s1a", "--crate-type=lib", "-O", "--emit=obj", p_asciz, "-o", p_asciz + ".o"],
            check=False,
        )

        p_quad = os.path.join(td, f"s1b_{tcs}.rs")
        Path(p_quad).write_text(
            r'''
#[export_name = "evil\"|0=rax\n.popsection\n#"]
pub extern "C" fn malicious_sym() {}
#[no_mangle]
pub unsafe fn test_sym_in_quad() {
    core::arch::asm!(
        "9996:\nlea rax, [rip + {s}]\n9997:\n.pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 777, {s}\n.popsection",
        s = sym malicious_sym, out("rax") _, options(nomem, nostack, preserves_flags),
    );
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=s1b", "--crate-type=lib", "-O", "--emit=obj", p_quad, "-o", p_quad + ".o"])
        elf_q = parse_elf64_reloc(p_quad + ".o")
        sh_q = {s["name"]: s for s in elf_q["shdrs"]}
        quad_sym = elf_q["relas"][sh_q[".anneal.asm_sites"]["idx"]][2]["sym_name"]

        # 2a vs 2b: numeric 9996: spoof hiding store vs Nonce + ${:uid} 4x-unrolled IR defense
        p_num = os.path.join(td, f"s2_{tcs}.rs")
        Path(p_num).write_text(
            r'''
#[no_mangle]
pub unsafe fn numeric_label_spoof(ptr: *mut u64, mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "9996:\nmov qword ptr [{p:r}], 0xdead\n9996:\nsub {a:r}, {b:r}\n9997:\n.pushsection .anneal.asm_sites,\"e\",@progbits\n.quad 9996b, 9997b, 888\n.popsection",
        p = in(reg) ptr, a = inout(reg) a, b = in(reg) b, options(pure, nomem, nostack),
    );
    a
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=s2", "--crate-type=lib", "-O", "--emit=obj", p_num, "-o", p_num + ".o"])
        elf_n = parse_elf64_reloc(p_num + ".o")
        sh_n = {s["name"]: s for s in elf_n["shdrs"]}
        rel_n = elf_n["relas"][sh_n[".anneal.asm_sites"]["idx"]]
        hidden_prefix_bytes = rel_n[0]["sym_value"] + rel_n[0]["r_addend"]

        p_ir = os.path.join(td, f"s2ir_{tcs}.rs")
        ll_p = os.path.join(td, f"s2ir_{tcs}.ll")
        Path(p_ir).write_text(
            r'''
#[inline(always)]
pub unsafe fn user_with_9996(ptr: *mut u64, mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "mov qword ptr [{0:r}], 0xdead\n9996:\nsub {1:r}, {2:r}",
        in(reg) ptr, inout(reg) a, in(reg) b, options(nomem, nostack),
    );
    a
}
#[no_mangle] #[inline(never)]
pub unsafe fn unrolled_nonce_uid(ptr: *mut u64, arr: &[u64; 4], mut acc: u64) -> u64 {
    let mut i = 0;
    while i < 4 { acc = user_with_9996(ptr, acc, arr[i]); i += 1; }
    acc
}
'''
        )
        run_cmd(["rustc", f"+{tc}", "--crate-name=s2ir", "--crate-type=lib", "-C", "opt-level=0", "--emit=llvm-ir", p_ir, "-o", ll_p])
        ll_txt = Path(ll_p).read_text()
        nonce = "9f4a2c81d70e3b56"
        m = re.search(r'asm sideeffect[^"]*"([^"]+)"', ll_txt)
        assert m is not None
        old_asm = m.group(1)
        wrapped_asm = (
            f".L__anneal_s_{nonce}_${{:uid}}:\\0A"
            + old_asm
            + f"\\0A.L__anneal_e_{nonce}_${{:uid}}:\\0A"
            + f".pushsection .anneal.asm_descs,\\22e\\22,@progbits\\0A"
            + f".L__anneal_d_{nonce}_${{:uid}}:\\0A"
            + f".asciz \\22{nonce}|uid=${{:uid}}|0=${{0:q}}|1=${{1:q}}|2=${{2:q}}\\22\\0A"
            + f".L__anneal_de_{nonce}_${{:uid}}:\\0A.popsection\\0A"
            + f".pushsection .anneal.asm_sites,\\22e\\22,@progbits\\0A"
            + f".quad .L__anneal_s_{nonce}_${{:uid}}, .L__anneal_e_{nonce}_${{:uid}}, 991, "
            + f".L__anneal_d_{nonce}_${{:uid}}, .L__anneal_de_{nonce}_${{:uid}} - .L__anneal_d_{nonce}_${{:uid}}, 0\\0A.popsection"
        )
        ll_mod_p = os.path.join(td, f"s2ir_mod_{tcs}.ll")
        obj_mod_p = os.path.join(td, f"s2ir_mod_{tcs}.o")
        Path(ll_mod_p).write_text(ll_txt.replace(f'"{old_asm}"', f'"{wrapped_asm}"').replace("optnone", ""))
        run_cmd(["clang-19", "-O3", "-c", "-x", "ir", ll_mod_p, "-o", obj_mod_p])
        elf_ir = parse_elf64_reloc(obj_mod_p)
        sh_ir = {s["name"]: s for s in elf_ir["shdrs"]}
        s_ir, d_ir = sh_ir[".anneal.asm_sites"], sh_ir[".anneal.asm_descs"]
        rel_ir = {r["r_offset"]: r for r in elf_ir["relas"][s_ir["idx"]]}
        nonce_uid_iters = []
        for k in range(0, s_ir["size"], 48):
            _, _, _, _, dlen, _ = struct.unpack_from("<QQQQQQ", s_ir["data"], k)
            rs, re_, rd = rel_ir[k], rel_ir[k + 8], rel_ir[k + 24]
            so, eo = rs["sym_value"] + rs["r_addend"], re_["sym_value"] + re_["r_addend"]
            do = rd["sym_value"] + rd["r_addend"]
            tsec = elf_ir["shdrs"][rs["sym_shndx"]]
            nonce_uid_iters.append(
                {
                    "span": [so, eo],
                    "byte_len": eo - so,
                    "hex": tsec["data"][so:eo].hex(),
                    "descriptor": d_ir["data"][do : do + dlen - 1].decode(),
                }
            )

        out[tc] = {
            "attested_sites": records,
            "spoof_matrix": {
                "sym_quote_in_asciz_rejected": r_asciz.returncode != 0,
                "sym_quote_in_quad_reloc_preserved": quad_sym == 'evil"|0=rax\n.popsection\n#',
                "numeric_9996_spoof_hidden_bytes": hidden_prefix_bytes,
                "nonce_uid_unrolled_4x_exposed_all_10_bytes": nonce_uid_iters,
            },
        }
    return out


def run_invariance_suite(td: str, toolchains: list[str]) -> dict[str, Any]:
    res: dict[str, Any] = {"x86_64": {}, "aarch64": {}}
    for tc in toolchains:
        tcs = tc.replace(".", "_")
        mode_hashes: dict[str, Any] = {}
        for mode in ["uninstrumented", "multiline_pushsection", "single_macro"]:
            hdr = (
                r'''core::arch::global_asm!(".macro __ar s, e, id, r0, r1\n.pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"0=\\r0|1=\\r1\"\n9999: .popsection\n.pushsection .anneal.asm_sites,\"e\",@progbits\n.quad \\s, \\e, \\id, 9998b, 9999b - 9998b, 0\n.popsection\n.endm");'''
                + "\n"
                if mode == "single_macro"
                else ""
            )

            def mk_x86(sid: int) -> str:
                if mode == "uninstrumented":
                    return '"sub {0:r}, {1:r}"'
                if mode == "multiline_pushsection":
                    return (
                        f'"9996:\\nsub {{0:r}}, {{1:r}}\\n9997:\\n'
                        f'.pushsection .anneal.asm_descs,\\x22e\\x22,@progbits\\n'
                        f'9998:\\n.asciz \\x220={{0:r}}|1={{1:r}}\\x22\\n9999:\\n.popsection\\n'
                        f'.pushsection .anneal.asm_sites,\\x22e\\x22,@progbits\\n'
                        f'.quad 9996b, 9997b, {sid}, 9998b, 9999b - 9998b, 0\\n.popsection"'
                    )
                return f'"9996: sub {{0:r}}, {{1:r}} ; 9997: __ar 9996b, 9997b, {sid}, {{0:r}}, {{1:r}}"'

            b35 = "\n".join(
                f"core::arch::asm!({mk_x86(i)}, inout(reg) a, in(reg) b, options(nomem, nostack));"
                for i in range(35)
            )
            post = "\n".join(
                'core::arch::asm!("xor {0:r}, {1:r}", inout(reg) a, in(reg) b, options(nomem, nostack));'
                for _ in range(15)
            )
            src = f"""#![no_std]
{hdr}
#[no_mangle]
pub unsafe fn true_rel8(cond: u64, mut a: u64, b: u64) -> u64 {{
    if cond != 0 {{ {b35} }}
    {post}
    a
}}
pub unsafe fn maybe_inlined(mut a: u64, b: u64) -> u64 {{
    {chr(10).join(f"core::arch::asm!({mk_x86(100+i)}, inout(reg) a, in(reg) b, options(nomem, nostack));" for i in range(12))}
    a.wrapping_mul(3).wrapping_add(b)
}}
#[no_mangle]
pub unsafe fn inline_caller(x: u64, y: u64) -> u64 {{
    maybe_inlined(x, y) ^ maybe_inlined(y, x)
}}
#[no_mangle]
pub unsafe fn unroll_16(arr: &[u64; 16], mut acc: u64) -> u64 {{
    let mut i = 0;
    while i < 16 {{
        core::arch::asm!({mk_x86(200)}, inout(reg) acc, in(reg) arr[i], options(nomem, nostack));
        i += 1;
    }}
    acc
}}
"""
            rp, op = os.path.join(td, f"inv_{tcs}_{mode}.rs"), os.path.join(td, f"inv_{tcs}_{mode}.o")
            Path(rp).write_text(src)
            run_cmd(["rustc", f"+{tc}", "--crate-name=inv", "--crate-type=lib", "-C", "opt-level=3", "-C", "codegen-units=1", "--emit=obj", rp, "-o", op])
            elf = parse_elf64_reloc(op)
            mode_hashes[mode] = {
                s["name"]: {"len": len(s["data"]), "sha256_16": hashlib.sha256(s["data"]).hexdigest()[:16]}
                for s in elf["shdrs"]
                if s["name"].startswith(".text.")
            }
        res["x86_64"][tc] = {
            "modes": mode_hashes,
            "exact_byte_parity_all_modes": (
                mode_hashes["uninstrumented"] == mode_hashes["multiline_pushsection"] == mode_hashes["single_macro"]
            ),
        }

    # AArch64 BranchRelaxation (`1.99.1 --target aarch64-unknown-linux-gnu`)
    targets_199 = run_cmd(["rustup", "target", "list", "--installed", "--toolchain", "1.99.1"]).stdout.splitlines()
    if "aarch64-unknown-linux-gnu" in targets_199:
        for n_blocks in [1200, 5000]:
            n_res: dict[str, Any] = {}
            for mode in ["uninstrumented", "multiline_pushsection", "two_stmt_macro", "zero_sep_site_macro"]:
                hdr = ""
                if mode == "two_stmt_macro":
                    hdr = r'''core::arch::global_asm!(".macro __aa s, e, id, r0\n.pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"0=\\r0\"\n9999: .popsection\n.pushsection .anneal.asm_sites,\"e\",@progbits\n.xword \\s, \\e, \\id, 9998b, 9999b - 9998b, 0\n.popsection\n.endm");''' + "\n"
                elif mode == "zero_sep_site_macro":
                    hdr = r'''core::arch::global_asm!(".macro __aw id, r0\n9996: add \\r0, \\r0, #1\n9997:\n.pushsection .anneal.asm_descs,\"e\",@progbits\n9998: .asciz \"0=\\r0\"\n9999: .popsection\n.pushsection .anneal.asm_sites,\"e\",@progbits\n.xword 9996b, 9997b, \\id, 9998b, 9999b - 9998b, 0\n.popsection\n.endm");''' + "\n"

                def mk_a64(sid: int) -> str:
                    if mode == "uninstrumented":
                        return '"add {0}, {0}, #1"'
                    if mode == "multiline_pushsection":
                        return (
                            f'"9996:\\nadd {{0}}, {{0}}, #1\\n9997:\\n'
                            f'.pushsection .anneal.asm_descs,\\x22e\\x22,@progbits\\n'
                            f'9998:\\n.asciz \\x220={{0}}\\x22\\n9999:\\n.popsection\\n'
                            f'.pushsection .anneal.asm_sites,\\x22e\\x22,@progbits\\n'
                            f'.xword 9996b, 9997b, {sid}, 9998b, 9999b - 9998b, 0\\n.popsection"'
                        )
                    if mode == "two_stmt_macro":
                        return f'"9996: add {{0}}, {{0}}, #1\\n9997: __aa 9996b, 9997b, {sid}, {{0}}"'
                    return f'"__aw {sid}, {{0}}"'

                bn = "\n".join(
                    f"core::arch::asm!({mk_a64(i)}, inout(reg) a, options(nomem, nostack, preserves_flags));"
                    for i in range(n_blocks)
                )
                post = "\n".join(
                    'core::arch::asm!("eor {0}, {0}, #3", inout(reg) a, options(nomem, nostack, preserves_flags));'
                    for _ in range(20)
                )
                src = f"#![no_std]\n{hdr}#[no_mangle]\npub unsafe fn true_tbz(flag: u64, mut a: u64) -> u64 {{\n    if (flag & 1) != 0 {{ {bn} }}\n    {post}\n    a\n}}\n"
                rp, op = os.path.join(td, f"a64_{n_blocks}_{mode}.rs"), os.path.join(td, f"a64_{n_blocks}_{mode}.o")
                Path(rp).write_text(src)
                run_cmd(["rustc", "+1.99.1", "--target", "aarch64-unknown-linux-gnu", "--crate-name=ta", "--crate-type=lib", "-C", "opt-level=3", "--emit=obj", rp, "-o", op])
                elf = parse_elf64_reloc(op)
                sh_map = {s["name"]: s for s in elf["shdrs"]}
                tb = sh_map[".text.true_tbz"]["data"]
                first_word = struct.unpack_from("<I", tb, 0)[0]
                is_single_tbz = (first_word >> 24) == 0x36
                n_res[mode] = {
                    "text_len": len(tb),
                    "sha256_16": hashlib.sha256(tb).hexdigest()[:16],
                    "entry_branch": "tbz_direct" if is_single_tbz else "tbnz_plus_b_relaxed",
                    "attested_records": len(sh_map.get(".anneal.asm_sites", {"data": b""})["data"]) // 48,
                }
            res["aarch64"][f"N_{n_blocks}"] = n_res
    return res


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchains", nargs="+", default=["1.99.1", "nightly"])
    parser.add_argument("--out", default="")
    args = parser.parse_args()

    with tempfile.TemporaryDirectory() as td:
        payload = {
            "probe_1_self_attesting_bindings": run_self_attestation_suite(td, args.toolchains),
            "probe_2_get_inline_asm_length_invariance": run_invariance_suite(td, args.toolchains),
        }
    rendered = json.dumps(payload, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(rendered)
    else:
        print(rendered, end="")


if __name__ == "__main__":
    main()
