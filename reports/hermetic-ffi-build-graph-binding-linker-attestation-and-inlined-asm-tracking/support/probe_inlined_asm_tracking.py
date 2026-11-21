#!/usr/bin/env python3
"""Executable probes for tracking and attesting inlined, CFG-cloned, and
loop-unrolled `asm!` sites in emitted `.o` binaries across `rustc -O`:
- 4A: Multi-caller inlining (distinct physical registers, REX bytes, spills/reloads)
- 4B: Intra-function CFG cloning / tail duplication (1 MIR InlineAsm -> 2+ machine copies)
- 4C: Loop unrolling of `asm!` (1 MIR InlineAsm -> 4 machine copies with distinct regs)
- 4D: AVX2 `vzeroupper` emission and placement divergence around `asm!`
- 4E: `#[inline(never)]` limitations (intra-fn unrolling, IPSCCP/const-prop specialization,
      `#[no_mangle]` inlining without `#[inline(never)]`, and linker `--icf=all` folding)
- 4F: Attestation mechanisms comparison:
      (1) `.pushsection` numeric-label (`1:`/`2:`) site-table byte extraction & decoding
      (2) DWARF `.debug_line` (`-C debuginfo=1`) interleaving/imprecision measurement
      (3) Out-of-line `#[unsafe(naked)]` `naked_asm!` 1:1 byte invariance.
"""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import re
import struct
import subprocess
import tempfile


def run(cmd: list[str], cwd: pathlib.Path | None = None, env: dict[str, str] | None = None, check: bool = True) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    if env:
        merged_env.update(env)
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        check=check,
    )


def disasm_symbol(obj_path: pathlib.Path, sym: str, line_numbers: bool = False) -> list[str]:
    cmd = ["llvm-objdump", "-d", f"--disassemble-symbols={sym}"]
    if line_numbers:
        cmd.append("-l")
    cmd.append(str(obj_path))
    txt = run(cmd).stdout
    lines = []
    for ln in txt.splitlines():
        s = ln.strip()
        if not s or s.startswith(str(obj_path)) or s.startswith("Disassembly of section"):
            continue
        lines.append(s)
    return lines


def probe_4a_4b_4c_inlining_cloning_unrolling(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe4abc_") as td:
        root = pathlib.Path(td)
        rs = root / "asm_opt.rs"
        rs.write_text(r'''
#![crate_type = "rlib"]
use core::arch::asm;

extern "C" {
    fn ext_barrier(a: u64, b: u64, c: u64, d: u64, e: u64, f: u64) -> u64;
}

#[inline(always)]
fn asm_mix(mut a: u64, b: u64) -> u64 {
    unsafe {
        asm!(
            "imul {0}, {1}",
            "xor {0}, 0x5a5a",
            inout(reg) a,
            in(reg) b,
            options(pure, nomem, nostack),
        );
    }
    a
}

#[no_mangle]
pub extern "C" fn caller_simple(x: u64, y: u64) -> u64 {
    asm_mix(x, y)
}

#[no_mangle]
pub extern "C" fn caller_high_pressure(
    a0: u64, a1: u64, a2: u64, a3: u64, a4: u64, a5: u64, p: *mut u64,
) -> u64 {
    let t = unsafe { ext_barrier(a5, a4, a3, a2, a1, a0) };
    let v1 = asm_mix(a3.wrapping_add(t), a5);
    let v2 = asm_mix(a4, a2.wrapping_add(v1));
    unsafe { *p = v1.wrapping_add(a0).wrapping_add(a1); }
    v2.wrapping_add(a0).wrapping_add(a1).wrapping_add(a2)
}

#[no_mangle]
pub extern "C" fn cfg_cloned_asm(cond: bool, x: u64, y: u64, z: u64) -> u64 {
    // Two distinct paths feeding into a small shared tail containing one MIR `asm!`;
    // LLVM tail-duplicates the small shared tail into both predecessors.
    let (mut a, b) = if cond {
        (x.wrapping_mul(3), y.wrapping_add(11))
    } else {
        (y.wrapping_mul(5), z.wrapping_add(29))
    };
    unsafe {
        asm!(
            "ror {0}, 13",
            "xor {0}, {1}",
            inout(reg) a,
            in(reg) b,
            options(pure, nomem, nostack),
        );
    }
    a
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn unrolled_loop_asm(arr: &[u64; 4], mut acc: u64) -> u64 {
    let mut i = 0;
    while i < 4 {
        let elem = arr[i];
        unsafe {
            asm!(
                "ror {0}, 7",
                "xor {0}, {1}",
                inout(reg) acc,
                in(reg) elem,
                options(pure, nomem, nostack),
            );
        }
        i += 1;
    }
    acc
}
''')
        obj = root / "asm_opt.o"
        mir_dir = root / "mir_dump"
        mir_dir.mkdir()
        run(
            [
                "rustc", f"+{toolchain}", "--edition=2021", "-O",
                "--emit=obj",
                "-Z", "dump-mir=runtime-post-cleanup",
                "-Z", f"dump-mir-dir={mir_dir}",
                str(rs), "-o", str(obj),
            ],
            env={"RUSTC_BOOTSTRAP": "1"},
        )

        # Count MIR asm! occurrences in runtime-post-cleanup dumps for cfg_cloned_asm and unrolled_loop_asm
        def count_mir_asm(fn_substr: str) -> int:
            for p in mir_dir.glob(f"*{fn_substr}*after.mir"):
                txt = p.read_text()
                return len(re.findall(r"\basm!\(", txt))
            return -1

        dis_simple = disasm_symbol(obj, "caller_simple")
        dis_press = disasm_symbol(obj, "caller_high_pressure")
        dis_cloned = disasm_symbol(obj, "cfg_cloned_asm")
        dis_unroll = disasm_symbol(obj, "unrolled_loop_asm")

        simple_xors = [ln for ln in dis_simple if "0x5a5a" in ln]
        press_xors = [ln for ln in dis_press if "0x5a5a" in ln]
        press_imuls = [ln for ln in dis_press if "imul" in ln]
        simple_imuls = [ln for ln in dis_simple if "imul" in ln]
        press_spills = [ln for ln in dis_press if "(%rsp)" in ln or "pushq" in ln]

        cloned_rors = [ln for ln in dis_cloned if "rorq" in ln and "$0xd" in ln]
        unroll_rors = [ln for ln in dis_unroll if "rorq" in ln and "$0x7" in ln]
        unroll_xors = [ln for ln in dis_unroll if "xorq" in ln]

        return {
            "4a_inlined_multi_caller": {
                "caller_simple_disasm": dis_simple,
                "caller_simple_imul_xor": simple_imuls + simple_xors,
                "caller_high_pressure_imul_xor": press_imuls + press_xors,
                "caller_high_pressure_spills_and_pushes": press_spills[:10],
                "distinct_encodings_or_regs": set(simple_imuls + simple_xors) != set(press_imuls + press_xors),
            },
            "4b_cfg_cloning": {
                "mir_post_cleanup_asm_count": count_mir_asm("cfg_cloned_asm"),
                "emitted_machine_ror_copies": len(cloned_rors),
                "emitted_ror_instructions": cloned_rors,
                "full_disasm": dis_cloned,
            },
            "4c_loop_unrolling": {
                "mir_post_cleanup_asm_count": count_mir_asm("unrolled_loop_asm"),
                "emitted_machine_ror_copies": len(unroll_rors),
                "emitted_ror_instructions": unroll_rors,
                "emitted_xor_instructions": unroll_xors,
                "full_disasm": dis_unroll,
            },
        }


def probe_4d_avx2_vzeroupper(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe4d_") as td:
        root = pathlib.Path(td)
        rs = root / "avx_asm.rs"
        rs.write_text(r'''
#![crate_type = "rlib"]
use core::arch::asm;
use core::arch::x86_64::{__m256i, _mm256_add_epi64, _mm256_loadu_si256, _mm256_storeu_si256};

#[inline(never)]
#[no_mangle]
pub extern "C" fn out_of_line_asm(mut x: u64) -> u64 {
    unsafe { asm!("add {0}, 1", inout(reg) x, options(pure, nomem, nostack)); }
    x
}

#[no_mangle]
pub unsafe extern "C" fn avx_inlined_plain_asm(p: *mut __m256i, mut x: u64) -> u64 {
    let a = _mm256_loadu_si256(p);
    let b = _mm256_loadu_si256(p.add(1));
    let c = _mm256_add_epi64(a, b);
    asm!("add {0}, 1", inout(reg) x, options(pure, nomem, nostack));
    _mm256_storeu_si256(p, c);
    x
}

#[no_mangle]
pub unsafe extern "C" fn avx_inlined_clobber_abi_asm(p: *mut __m256i, mut x: u64) -> u64 {
    let a = _mm256_loadu_si256(p);
    let b = _mm256_loadu_si256(p.add(1));
    let c = _mm256_add_epi64(a, b);
    asm!("add rax, 1", inlateout("rax") x, clobber_abi("C"), options(nomem, nostack));
    _mm256_storeu_si256(p, c);
    x
}

#[no_mangle]
pub unsafe extern "C" fn avx_calling_outline_asm(p: *mut __m256i, x: u64) -> u64 {
    let a = _mm256_loadu_si256(p);
    let b = _mm256_loadu_si256(p.add(1));
    let c = _mm256_add_epi64(a, b);
    let r = out_of_line_asm(x);
    _mm256_storeu_si256(p, c);
    r
}
''')
        obj = root / "avx_asm.o"
        run(["rustc", f"+{toolchain}", "--edition=2021", "-O", "-C", "target-feature=+avx2", "--emit=obj", str(rs), "-o", str(obj)])
        out = {}
        for fn in ("avx_inlined_plain_asm", "avx_inlined_clobber_abi_asm", "avx_calling_outline_asm"):
            dis = disasm_symbol(obj, fn)
            vz = [ln for ln in dis if "vzeroupper" in ln]
            out[fn] = {
                "vzeroupper_count": len(vz),
                "vzeroupper_lines": vz,
                "disasm": dis,
            }
        return out


def probe_4e_inline_never_limitations(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe4e_") as td:
        root = pathlib.Path(td)
        rs = root / "inline_never_limits.rs"
        rs.write_text(r'''
use core::arch::asm;

// 1. Non-exported #[inline(never)] always called with constant b = 0x1337
#[inline(never)]
fn internal_never_inline(mut a: u64, b: u64) -> u64 {
    unsafe {
        asm!(
            "add {0}, {1}",
            inout(reg) a,
            in(reg) b,
            options(pure, nomem, nostack),
        );
    }
    a
}

// 2. #[no_mangle] WITHOUT #[inline(never)]
#[no_mangle]
pub extern "C" fn exported_no_inline_never(mut x: u64) -> u64 {
    unsafe {
        asm!("xor {0}, 0x2468", inout(reg) x, options(pure, nomem, nostack));
    }
    x
}

#[no_mangle]
pub extern "C" fn caller_of_exported(x: u64) -> u64 {
    exported_no_inline_never(x).wrapping_add(1)
}

#[no_mangle]
pub extern "C" fn caller_of_internal_1(x: u64) -> u64 {
    internal_never_inline(x, 0x1337)
}

#[no_mangle]
pub extern "C" fn caller_of_internal_2(x: u64) -> u64 {
    internal_never_inline(x.wrapping_mul(3), 0x1337)
}

// 3. Two distinct #[no_mangle] #[inline(never)] functions with identical asm! bodies for ICF test
#[no_mangle]
#[inline(never)]
pub extern "C" fn icf_target_alpha(mut x: u64) -> u64 {
    unsafe { asm!("xor {0}, 0x7777", inout(reg) x, options(pure, nomem, nostack)); }
    x
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn icf_target_beta(mut x: u64) -> u64 {
    unsafe { asm!("xor {0}, 0x7777", inout(reg) x, options(pure, nomem, nostack)); }
    x
}

fn main() {
    let v = std::hint::black_box(10u64);
    println!("{} {} {} {} {}",
        caller_of_exported(v),
        caller_of_internal_1(v),
        caller_of_internal_2(v),
        icf_target_alpha(v),
        icf_target_beta(v),
    );
}
''')
        obj = root / "limits.o"
        run(["rustc", f"+{toolchain}", "--edition=2021", "-O", "-C", "codegen-units=1", "--emit=obj", str(rs), "-o", str(obj)])
        dis_caller_exp = disasm_symbol(obj, "caller_of_exported")
        # Find mangled internal_never_inline symbol
        nm_out = run(["nm", str(obj)]).stdout
        internal_syms = [ln.split()[-1] for ln in nm_out.splitlines() if "internal_never_inline" in ln]
        dis_internal = disasm_symbol(obj, internal_syms[0]) if internal_syms else []

        # Check MergeFunctions aliasing directly inside limits.o (before linking!)
        obj_sym_lines = [ln for ln in run(["readelf", "-sW", str(obj)]).stdout.splitlines() if "icf_target_" in ln]
        # Link with --icf=all vs --icf=safe vs --icf=none
        icf_res = {}
        for mode in ("none", "safe", "all"):
            exe = root / f"app_icf_{mode}"
            run(["rustc", f"+{toolchain}", "--edition=2021", "-O", "-C", "codegen-units=1", "-C", f"link-arg=-Wl,--icf={mode}", str(rs), "-o", str(exe)])
            syms = run(["nm", str(exe)]).stdout
            addrs = {}
            for ln in syms.splitlines():
                parts = ln.split()
                if len(parts) >= 3 and parts[2] in ("icf_target_alpha", "icf_target_beta"):
                    addrs[parts[2]] = parts[0]
            icf_res[mode] = {
                "addresses": addrs,
                "folded_to_identical_vma": (addrs.get("icf_target_alpha") == addrs.get("icf_target_beta")) and bool(addrs),
            }

        insn_lines = [ln for ln in dis_caller_exp if not ln.endswith(":")]
        return {
            "exported_without_inline_never_was_inlined_into_caller": any("0x2468" in ln for ln in insn_lines) and not any("\tcall" in ln or "\tjmp" in ln for ln in insn_lines),
            "caller_of_exported_disasm": dis_caller_exp,
            "internal_never_inline_symbol": internal_syms[0] if internal_syms else None,
            "internal_never_inline_const_specialized_0x1337": any("1337" in ln for ln in dis_internal),
            "internal_never_inline_disasm": dis_internal,
            "obj_merge_functions_symtab_lines": obj_sym_lines,
            "linker_icf_folding": icf_res,
        }


def parse_elf64_sections_and_relas(obj_path: pathlib.Path) -> tuple[dict[int, dict], dict[str, int], list[dict]]:
    """Parses ELF64 sections, symbol table, and RELA entries for .anneal.asm_sites."""
    data = obj_path.read_bytes()
    e_shoff, = struct.unpack_from("<Q", data, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
    shstr_off = e_shoff + e_shstrndx * e_shentsize
    _, _, _, _, shstr_foff, shstr_sz = struct.unpack_from("<IIQQQQ", data, shstr_off)
    shstr = data[shstr_foff : shstr_foff + shstr_sz]

    def cstr(tbl: bytes, off: int) -> str:
        end = tbl.find(b"\x00", off)
        return tbl[off:end].decode("utf-8", errors="replace") if end != -1 else tbl[off:].decode("utf-8", errors="replace")

    secs = {}
    name_to_idx = {}
    symtab_idx = None
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, _, sh_entsize = struct.unpack_from("<IIQQQQIIQQ", data, off)
        name = cstr(shstr, sh_name)
        secs[i] = {
            "idx": i, "name": name, "type": sh_type, "flags": sh_flags,
            "offset": sh_offset, "size": sh_size, "link": sh_link, "info": sh_info, "entsize": sh_entsize,
            "bytes": data[sh_offset : sh_offset + sh_size] if sh_type != 8 else b"",
        }
        name_to_idx[name] = i
        if sh_type == 2:
            symtab_idx = i

    syms = []
    if symtab_idx is not None:
        st_sec = secs[symtab_idx]
        strtab = secs[st_sec["link"]]["bytes"]
        for pos in range(0, st_sec["size"], st_sec["entsize"]):
            st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from("<IBBHQQ", st_sec["bytes"], pos)
            syms.append({
                "name": cstr(strtab, st_name),
                "shndx": st_shndx,
                "value": st_value,
                "size": st_size,
            })

    return secs, name_to_idx, syms


def probe_4f_attestation_mechanisms(toolchain: str) -> dict:
    """Prototypes and compares:
    1) `.pushsection .anneal.asm_sites` with numeric local labels `9998:` / `9999:`
       across multi-caller inlining, CFG cloning, and 4x loop unrolling — proving
       exact byte-range extraction and decoding of every emitted machine instance!
    2) DWARF `.debug_line` (`-C debuginfo=1`) interleaving on unrolled `asm!`.
    3) Out-of-line `#[unsafe(naked)]` `naked_asm!` 1:1 byte invariance.
    """
    with tempfile.TemporaryDirectory(prefix="probe4f_") as td:
        root = pathlib.Path(td)
        rs = root / "attest.rs"
        rs.write_text(r'''
#![crate_type = "rlib"]
use core::arch::{asm, naked_asm};

#[inline(always)]
fn attested_mix(mut a: u64, b: u64) -> u64 {
    unsafe {
        asm!(
            "9998:",
            "imul {0}, {1}",
            "xor {0}, 0x5a5a",
            "9999:",
            ".pushsection .anneal.asm_sites,\"e\",@progbits",
            ".quad 9998b",
            ".quad 9999b",
            ".quad 0xA11EA101",
            ".popsection",
            inout(reg) a,
            in(reg) b,
            options(pure, nomem, nostack),
        );
    }
    a
}

#[no_mangle]
pub extern "C" fn inlined_caller_1(x: u64, y: u64) -> u64 {
    attested_mix(x, y)
}

#[no_mangle]
pub extern "C" fn inlined_caller_2(x: u64, y: u64, z: u64) -> u64 {
    let t = attested_mix(z, x);
    attested_mix(y, t)
}

#[no_mangle]
pub extern "C" fn unrolled_attested(arr: &[u64; 4], mut acc: u64) -> u64 {
    let mut i = 0;
    while i < 4 {
        let e = arr[i];
        unsafe {
            asm!(
                "9998:",
                "ror {0}, 7",
                "xor {0}, {1}",
                "9999:",
                ".pushsection .anneal.asm_sites,\"e\",@progbits",
                ".quad 9998b",
                ".quad 9999b",
                ".quad 0xA11EA102",
                ".popsection",
                inout(reg) acc,
                in(reg) e,
                options(pure, nomem, nostack),
            );
        }
        i += 1;
    }
    acc
}

// Dead pure asm! to verify LLVM DCE eliminates both code AND its .pushsection record
#[no_mangle]
pub extern "C" fn dead_pure_asm_caller(x: u64, y: u64) -> u64 {
    let _unused = attested_mix(x, y);
    x.wrapping_add(1)
}

// Out-of-line naked_asm! for 1:1 byte invariance comparison
#[unsafe(naked)]
#[no_mangle]
pub extern "C" fn naked_mix_fixed(a: u64, b: u64) -> u64 {
    naked_asm!(
        "imul rdi, rsi",
        "xor rdi, 0x5a5a",
        "mov rax, rdi",
        "ret",
    );
}
''')
        obj = root / "attest.o"
        run(["rustc", f"+{toolchain}", "--edition=2021", "-O", "-C", "debuginfo=1", "--emit=obj", str(rs), "-o", str(obj)])

        secs, name_to_idx, syms = parse_elf64_sections_and_relas(obj)
        sites_idx = name_to_idx[".anneal.asm_sites"]
        sites_bytes = secs[sites_idx]["bytes"]
        rela_idx = name_to_idx[".rela.anneal.asm_sites"]
        rela_bytes = secs[rela_idx]["bytes"]

        # Map each 8-byte offset in .anneal.asm_sites -> (target_sec_name, target_sec_idx, offset_in_sec)
        reloc_map = {}
        for pos in range(0, len(rela_bytes), 24):
            r_offset, r_info, r_addend = struct.unpack_from("<QQq", rela_bytes, pos)
            sym_idx = r_info >> 32
            sym = syms[sym_idx]
            target_sec = secs[sym["shndx"]]
            reloc_map[r_offset] = (target_sec["name"], sym["shndx"], sym["value"] + r_addend)

        records = []
        n_recs = len(sites_bytes) // 24
        for idx in range(n_recs):
            base = idx * 24
            site_id, = struct.unpack_from("<Q", sites_bytes, base + 16)
            sec_s, s_idx, start_off = reloc_map[base]
            sec_e, e_idx, end_off = reloc_map[base + 8]
            assert s_idx == e_idx and end_off > start_off
            raw_slice = secs[s_idx]["bytes"][start_off:end_off]
            # Disassemble the exact extracted byte slice via llvm-mc!
            hex_in = " ".join(f"0x{b:02x}" for b in raw_slice)
            mc_p = subprocess.run(
                ["llvm-mc", "-disassemble", "-triple=x86_64-unknown-linux-gnu", "-x86-asm-syntax=intel"],
                input=hex_in + "\n",
                text=True,
                capture_output=True,
            )
            insns = [ln.strip() for ln in mc_p.stdout.splitlines() if ln.strip() and not ln.strip().startswith(".text")]
            records.append({
                "record_index": idx,
                "site_id": hex(site_id),
                "enclosing_section": sec_s,
                "start_offset": start_off,
                "end_offset": end_off,
                "byte_len": len(raw_slice),
                "raw_bytes_hex": raw_slice.hex(),
                "decoded_insns": insns,
            })

        # Verify SHF_EXCLUDE ("e") section is stripped from final linked ELF cleanly even under --gc-sections!
        main_rs = root / "link_check.rs"
        main_rs.write_text(
            'extern "C" { fn inlined_caller_1(x: u64, y: u64) -> u64; fn unrolled_attested(a: &[u64; 4], s: u64) -> u64; fn naked_mix_fixed(a: u64, b: u64) -> u64; }\n'
            'fn main() {\n'
            '    let arr = [1u64, 2, 3, 4];\n'
            '    println!("{} {} {}", unsafe { inlined_caller_1(3, 4) }, unsafe { unrolled_attested(&arr, 5) }, unsafe { naked_mix_fixed(3, 4) });\n'
            '}\n'
        )
        link_gc_results = {}
        for lname, extra in [("rust_lld", []), ("ld_bfd", ["-C", "link-arg=-fuse-ld=bfd"])]:
            exe = root / f"link_check_{lname}"
            link_p = run(
                ["rustc", f"+{toolchain}", "--edition=2021", "-O", "-C", f"link-arg={obj}", "-C", "link-arg=-Wl,--gc-sections", *extra, str(main_rs), "-o", str(exe)],
                check=False,
            )
            linked_secs = run(["readelf", "-SW", str(exe)]).stdout if link_p.returncode == 0 else ""
            linked_syms = run(["nm", str(exe)]).stdout if link_p.returncode == 0 else ""
            link_gc_results[lname] = {
                "rc": link_p.returncode,
                "shf_exclude_stripped_from_final_exe": ".anneal.asm_sites" not in linked_secs,
                "unreferenced_inlined_caller_2_gc_collected": "inlined_caller_2" not in linked_syms,
                "final_exe_output": run([str(exe)]).stdout.strip() if link_p.returncode == 0 else None,
            }

        # DWARF .debug_line inspection on unrolled_attested
        dwarf_dis = disasm_symbol(obj, "unrolled_attested", line_numbers=True)

        # Out-of-line naked_mix_fixed bytes
        naked_sec = secs[name_to_idx[".text.naked_mix_fixed"]]["bytes"]

        return {
            "pushsection_site_table": {
                "section_flags_hex": hex(secs[sites_idx]["flags"]),
                "has_SHF_EXCLUDE": bool(secs[sites_idx]["flags"] & 0x80000000),
                "total_emitted_records": n_recs,
                "expected_records_1_plus_2_plus_4_and_0_for_dead": n_recs == 7,
                "dead_pure_asm_emitted_zero_records": not any("dead_pure_asm_caller" in r["enclosing_section"] for r in records),
                "records": records,
                "gc_sections_link_checks": link_gc_results,
            },
            "dwarf_debug_line_unrolled": dwarf_dis,
            "naked_asm_fixed_bytes_hex": naked_sec.hex(),
            "naked_asm_disasm": disasm_symbol(obj, "naked_mix_fixed"),
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchains", nargs="+", default=["1.99.1", "nightly-2026-06-01"])
    parser.add_argument("--json-out", type=pathlib.Path)
    args = parser.parse_args()

    out = {}
    for tc in args.toolchains:
        out[tc] = {
            "probe_4abc": probe_4a_4b_4c_inlining_cloning_unrolling(tc),
            "probe_4d_avx2_vzeroupper": probe_4d_avx2_vzeroupper(tc),
            "probe_4e_inline_never_limitations": probe_4e_inline_never_limitations(tc),
            "probe_4f_attestation_mechanisms": probe_4f_attestation_mechanisms(tc),
        }

    rendered = json.dumps(out, indent=2)
    if args.json_out:
        args.json_out.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
