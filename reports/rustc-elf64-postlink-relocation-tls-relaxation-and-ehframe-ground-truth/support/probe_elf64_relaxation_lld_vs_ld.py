#!/usr/bin/env python3
"""Head-to-head ELF64 post-link relaxation, sysroot census, and .eh_frame_hdr probe.

Compares GNU ld against rust-lld across dynamic PIE (relax and --no-relax),
static PIE (+crt-static and freestanding #![no_std] -static-pie), and cdylib
modes, verifies raw .eh_frame_hdr binary-search table layout against FDE
initial_location fields, and cross-checks the rustc sysroot .rlib relocation
census against a preserved rustc 1.102.0-nightly baseline if provided.
"""

from __future__ import annotations

import argparse
import glob
import json
import os
import re
import resource
import shutil
import struct
import subprocess
import tempfile
import time
from pathlib import Path
from typing import Any

RELOC_LINE_RE = re.compile(
    r"^\s*([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+(R_X86_64_\S+)\s+([0-9a-fA-F]+)\s*(.*)$"
)
SEC_HDR_RE = re.compile(r"^Relocation section '([^']+)'")
OBJDUMP_INSN_RE = re.compile(
    r"^\s*([0-9a-fA-F]+):\t([0-9a-fA-F]{2}(?:\s+[0-9a-fA-F]{2})*)\s*(?:\t(.*))?$"
)
OBJDUMP_RELOC_RE = re.compile(r"^\s*([0-9a-fA-F]+):\s+(R_X86_64_\S+)\s+(.*)$")
SECTION_ROW_RE = re.compile(
    r"^\s*\[\s*\d+\]\s+(\.\S+)\s+(\S+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+"
)

RELAXABLE_RELOCS = frozenset(
    {
        "R_X86_64_GOTTPOFF",
        "R_X86_64_TLSGD",
        "R_X86_64_TLSLD",
        "R_X86_64_GOTPCRELX",
        "R_X86_64_REX_GOTPCRELX",
        "R_X86_64_GOTPC32_TLSDESC",
        "R_X86_64_TLSDESC_CALL",
        "R_X86_64_CODE_4_GOTPCRELX",
        "R_X86_64_CODE_4_GOTTPOFF",
        "R_X86_64_CODE_6_GOTTPOFF",
    }
)


def sanitize_text(text: str, home_dir: str, sysroot_dir: str) -> str:
    """Replace host-specific home and sysroot paths with stable placeholders."""
    if sysroot_dir:
        text = text.replace(sysroot_dir, "<SYSROOT>")
    if home_dir:
        text = text.replace(home_dir, "<HOME>")
    return text


def run_timed(cmd: list[str], env: dict[str, str] | None = None) -> dict[str, Any]:
    """Run subprocess while capturing wall time, child user/sys time, and peak RSS."""
    t0 = time.monotonic()
    r_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    proc = subprocess.run(cmd, env=env, text=True, capture_output=True)
    r_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    elapsed = time.monotonic() - t0
    return {
        "rc": proc.returncode,
        "stdout": proc.stdout,
        "stderr": proc.stderr,
        "elapsed_sec": round(elapsed, 4),
        "child_maxrss_kib": r_after.ru_maxrss,
        "user_sec": round(max(0.0, r_after.ru_utime - r_before.ru_utime), 4),
        "sys_sec": round(max(0.0, r_after.ru_stime - r_before.ru_stime), 4),
    }


def scan_sysroot_rlibs(sysroot_dir: str) -> dict[str, Any]:
    """Census all ELF64 relocations across every sysroot .rlib on x86_64-unknown-linux-gnu."""
    lib_dir = Path(sysroot_dir) / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "lib"
    rlibs = sorted(lib_dir.glob("*.rlib"))
    by_type: dict[str, int] = {}
    by_section_class: dict[str, dict[str, int]] = {
        "text": {},
        "eh_frame": {},
        "debug": {},
        "data_rodata": {},
    }
    relaxable_by_rlib: dict[str, dict[str, int]] = {}
    sample_symbols: dict[str, list[str]] = {}

    for rlib in rlibs:
        # readelf exits 1 on .rlib archives because lib.rmeta is not ELF, while still
        # dumping every ELF member's relocation sections to stdout.
        res = subprocess.run(["readelf", "-rW", str(rlib)], text=True, capture_output=True)
        cur_sec = ""
        rname = rlib.name
        stem = rname.split("-", 1)[0]
        for line in res.stdout.splitlines():
            sm = SEC_HDR_RE.match(line)
            if sm:
                cur_sec = sm.group(1)
                continue
            m = RELOC_LINE_RE.match(line)
            if not m:
                continue
            rtype = m.group(3)
            sym = m.group(5).strip()
            by_type[rtype] = by_type.get(rtype, 0) + 1
            if ".eh_frame" in cur_sec:
                sclass = "eh_frame"
            elif ".debug" in cur_sec:
                sclass = "debug"
            elif ".text" in cur_sec:
                sclass = "text"
            else:
                sclass = "data_rodata"
            by_section_class[sclass][rtype] = by_section_class[sclass].get(rtype, 0) + 1
            if rtype in RELAXABLE_RELOCS:
                relaxable_by_rlib.setdefault(rname, {})[rtype] = (
                    relaxable_by_rlib.get(rname, {}).get(rtype, 0) + 1
                )
                key = f"{stem}:{rtype}"
                syms = sample_symbols.setdefault(key, [])
                if sym and sym not in syms and len(syms) < 3:
                    syms.append(sym)

    sorted_types = dict(sorted(by_type.items(), key=lambda kv: (-kv[1], kv[0])))
    sorted_rlibs = {
        k: dict(sorted(v.items())) for k, v in sorted(relaxable_by_rlib.items())
    }
    return {
        "rlib_count": len(rlibs),
        "distinct_reloc_types": len(sorted_types),
        "total_relocations": sum(sorted_types.values()),
        "by_type": sorted_types,
        "by_section_class": {
            k: dict(sorted(v.items(), key=lambda kv: (-kv[1], kv[0])))
            for k, v in by_section_class.items()
        },
        "opcode_relaxable_total": sum(
            v for inner in sorted_rlibs.values() for v in inner.values()
        ),
        "relaxable_by_rlib": sorted_rlibs,
        "sample_relaxable_symbols": dict(sorted(sample_symbols.items())),
    }


def parse_dynamic_relocs(path: Path) -> dict[str, int]:
    """Count dynamic/object relocation types in an ELF file via readelf -rW."""
    res = subprocess.run(["readelf", "-rW", str(path)], text=True, capture_output=True)
    counts: dict[str, int] = {}
    for line in res.stdout.splitlines():
        m = RELOC_LINE_RE.match(line)
        if m:
            rt = m.group(3)
            counts[rt] = counts.get(rt, 0) + 1
    return dict(sorted(counts.items(), key=lambda kv: (-kv[1], kv[0])))


def parse_objdump_function(path: Path, fn_names: list[str], with_relocs: bool) -> dict[str, Any]:
    """Disassemble target functions and extract instruction bytes, relocs, and alignment padding."""
    cmd = ["objdump", "-dr" if with_relocs else "-d", str(path)]
    out = subprocess.check_output(cmd, text=True)
    targets = set(fn_names)
    result: dict[str, Any] = {}
    cur_fn: str | None = None
    cur_insns: list[dict[str, Any]] = []
    cur_start: int | None = None

    def flush() -> None:
        nonlocal cur_fn, cur_insns, cur_start
        if cur_fn is None:
            return
        real_insns = [
            ins
            for ins in cur_insns
            if not (ins["asm"].startswith("nop") or ins["asm"].startswith("cs nop") or ins["asm"].startswith("data16 nop") or ins["asm"].startswith("int3"))
        ]
        # Strip trailing alignment padding instructions (int3 / multi-byte nop) after final instruction
        trimmed = list(cur_insns)
        while trimmed and (
            trimmed[-1]["asm"] == "int3"
            or trimmed[-1]["asm"].startswith("nop")
            or trimmed[-1]["asm"].startswith("cs nop")
            or trimmed[-1]["asm"].startswith("data16 nop")
            or trimmed[-1]["asm"].startswith("xchg   %ax,%ax")
        ):
            trimmed.pop()
        pad_insns = cur_insns[len(trimmed) :]
        body_bytes = [b for ins in trimmed for b in ins["bytes"].split()]
        pad_bytes = [b for ins in pad_insns for b in ins["bytes"].split()]
        result[cur_fn] = {
            "base_addr": hex(cur_start) if cur_start is not None else "0x0",
            "insn_count": len(trimmed),
            "code_bytes_len": len(body_bytes),
            "code_bytes_hex": " ".join(body_bytes),
            "pad_bytes_len": len(pad_bytes),
            "pad_bytes_hex": " ".join(pad_bytes),
            "insns": trimmed,
            "pad_insns": pad_insns,
            "all_raw_insns_count": len(cur_insns),
            "non_pad_count": len(real_insns),
        }
        cur_fn = None
        cur_insns = []
        cur_start = None

    hdr_re = re.compile(r"^([0-9a-fA-F]+)\s+<([^>]+)>:\s*$")
    for line in out.splitlines():
        hm = hdr_re.match(line)
        if hm:
            flush()
            name = hm.group(2)
            if name in targets:
                cur_fn = name
                cur_start = int(hm.group(1), 16)
            continue
        if cur_fn is None:
            continue
        if not line.strip():
            flush()
            continue
        rm = OBJDUMP_RELOC_RE.match(line)
        if rm and cur_insns:
            cur_insns[-1]["relocs"].append(
                {
                    "offset": hex(int(rm.group(1), 16)),
                    "rel_to_fn": hex(int(rm.group(1), 16) - (cur_start or 0)),
                    "type": rm.group(2),
                    "target": rm.group(3).strip(),
                }
            )
            continue
        im = OBJDUMP_INSN_RE.match(line)
        if im:
            addr = int(im.group(1), 16)
            bytes_list = im.group(2).split()
            asm_str = " ".join((im.group(3) or "").split())
            if cur_insns and not asm_str:
                # Objdump continuation line for instructions > 7 bytes
                cur_insns[-1]["bytes"] = cur_insns[-1]["bytes"] + " " + " ".join(bytes_list)
                cur_insns[-1]["byte_len"] += len(bytes_list)
            else:
                cur_insns.append(
                    {
                        "addr": hex(addr),
                        "rel_off": hex(addr - (cur_start or 0)),
                        "bytes": " ".join(bytes_list),
                        "byte_len": len(bytes_list),
                        "asm": asm_str,
                        "relocs": [],
                    }
                )
    flush()
    return result


def read_elf64_sections_and_verify_eh_frame_hdr(path: Path) -> dict[str, Any]:
    """Parse ELF64 section headers, verify .eh_frame_hdr binary-search table and FDE PCs."""
    data = path.read_bytes()
    e_ident = data[:16]
    if e_ident[:4] != b"\x7fELF" or e_ident[4] != 2 or e_ident[5] != 1:
        raise ValueError(f"{path}: expected 64-bit little-endian ELF")
    e_shoff, = struct.unpack_from("<Q", data, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
    shdrs = []
    for idx in range(e_shnum):
        off = e_shoff + idx * e_shentsize
        shdrs.append(struct.unpack_from("<IIQQQQIIQQ", data, off))
    shstr_off = shdrs[e_shstrndx][4]
    shstr_size = shdrs[e_shstrndx][5]
    shstr = data[shstr_off : shstr_off + shstr_size]

    def sec_name(name_off: int) -> str:
        end = shstr.find(b"\x00", name_off)
        return shstr[name_off:end].decode("ascii", errors="replace")

    sections: dict[str, dict[str, Any]] = {}
    for sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, _, _, sh_addralign, _ in shdrs:
        name = sec_name(sh_name)
        if name:
            sections[name] = {
                "sh_type": sh_type,
                "sh_flags": sh_flags,
                "addr": sh_addr,
                "offset": sh_offset,
                "size": sh_size,
                "align": sh_addralign,
            }

    # Count CIEs/FDEs from readelf --debug-dump=frames
    frames = subprocess.run(["readelf", "--debug-dump=frames", str(path)], text=True, capture_output=True)
    cie_count = sum(1 for l in frames.stdout.splitlines() if re.match(r"^[0-9a-fA-F]+\s+[0-9a-fA-F]+\s+00000000\s+CIE\b", l))
    fde_count_dump = sum(1 for l in frames.stdout.splitlines() if re.match(r"^[0-9a-fA-F]+\s+[0-9a-fA-F]+\s+[0-9a-fA-F]+\s+FDE\b", l))

    hdr_sec = sections[".eh_frame_hdr"]
    eh_sec = sections[".eh_frame"]
    hdr_bytes = data[hdr_sec["offset"] : hdr_sec["offset"] + hdr_sec["size"]]
    version, eh_ptr_enc, fde_cnt_enc, table_enc = struct.unpack_from("<BBBB", hdr_bytes, 0)
    eh_frame_ptr_rel, fde_count = struct.unpack_from("<iI", hdr_bytes, 4)
    decoded_eh_va = hdr_sec["addr"] + 4 + eh_frame_ptr_rel

    entries: list[dict[str, Any]] = []
    strictly_sorted = True
    prev_pc: int | None = None
    fde_pc_mismatches = 0
    neg_keys = 0
    pos_keys = 0

    for i in range(fde_count):
        init_loc_rel, fde_ptr_rel = struct.unpack_from("<ii", hdr_bytes, 12 + i * 8)
        entry_pc = hdr_sec["addr"] + init_loc_rel
        fde_va = hdr_sec["addr"] + fde_ptr_rel
        fde_file_off = eh_sec["offset"] + (fde_va - eh_sec["addr"])
        # At fde_file_off: length(4), cie_pointer(4), pc_begin(sdata4, DW_EH_PE_pcrel|sdata4 relative to fde_va+8)
        fde_len, fde_cie_ptr, fde_pc_begin_rel = struct.unpack_from("<IIi", data, fde_file_off)
        fde_pc = (fde_va + 8) + fde_pc_begin_rel
        if fde_pc != entry_pc:
            fde_pc_mismatches += 1
        if prev_pc is not None and not (prev_pc < entry_pc):
            strictly_sorted = False
        prev_pc = entry_pc
        if init_loc_rel < 0:
            neg_keys += 1
        else:
            pos_keys += 1
        entries.append(
            {
                "index": i,
                "init_loc_rel": init_loc_rel,
                "fde_ptr_rel": fde_ptr_rel,
                "entry_pc_hex": hex(entry_pc),
                "fde_va_hex": hex(fde_va),
                "fde_pc_begin_rel": fde_pc_begin_rel,
                "fde_pc_hex": hex(fde_pc),
            }
        )

    keep_secs = [".text", ".rodata", ".eh_frame_hdr", ".eh_frame", ".got", ".got.plt", ".plt", ".rela.dyn", ".rela.plt", ".gcc_except_table"]
    sec_summary = {
        s: {
            "addr": hex(sections[s]["addr"]),
            "offset": hex(sections[s]["offset"]),
            "size": sections[s]["size"],
            "sh_type": sections[s]["sh_type"],
        }
        for s in keep_secs
        if s in sections
    }

    return {
        "sections": sec_summary,
        "cie_count": cie_count,
        "fde_count_readelf": fde_count_dump,
        "eh_frame_hdr": {
            "version": version,
            "eh_frame_ptr_enc": hex(eh_ptr_enc),
            "fde_count_enc": hex(fde_cnt_enc),
            "table_enc": hex(table_enc),
            "eh_frame_ptr_rel": eh_frame_ptr_rel,
            "decoded_eh_frame_va": hex(decoded_eh_va),
            "actual_eh_frame_va": hex(eh_sec["addr"]),
            "eh_frame_ptr_matches": decoded_eh_va == eh_sec["addr"],
            "fde_count": fde_count,
            "strictly_sorted_pc": strictly_sorted,
            "fde_pc_mismatches": fde_pc_mismatches,
            "neg_init_loc_rel_count": neg_keys,
            "pos_init_loc_rel_count": pos_keys,
            "sample_first_4_entries": entries[:4],
            "sample_last_2_entries": entries[-2:],
            "header_12B_hex": " ".join(f"{b:02x}" for b in hdr_bytes[:12]),
        },
    }


def count_text_padding_distribution(path: Path) -> dict[str, int]:
    """Count inter-function padding opcodes inside .text via objdump -d."""
    out = subprocess.check_output(["objdump", "-d", "-j", ".text", str(path)], text=True)
    counts = {"int3_insns": 0, "nop_insns": 0}
    for line in out.splitlines():
        m = OBJDUMP_INSN_RE.match(line)
        if not m:
            continue
        asm = " ".join((m.group(3) or "").split())
        if asm == "int3":
            counts["int3_insns"] += 1
        elif asm == "nop" or asm.startswith("nopl") or asm.startswith("nopw") or asm.startswith("cs nopw") or asm.startswith("data16 nopw") or asm == "xchg   %ax,%ax":
            counts["nop_insns"] += 1
    return counts


def run_probes(baseline_json: str | None) -> dict[str, Any]:
    home_dir = os.path.expanduser("~")
    sysroot = subprocess.check_output(["rustc", "--print", "sysroot"], text=True).strip()
    rustc_ver = subprocess.check_output(["rustc", "--version", "--verbose"], text=True).strip()
    gnu_ld_ver = subprocess.check_output(["ld", "--version"], text=True).splitlines()[0].strip()
    rust_lld_bin = Path(sysroot) / "lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld"
    lld_ver = subprocess.check_output([str(rust_lld_bin), "-flavor", "gnu", "--version"], text=True).strip()

    census_live = scan_sysroot_rlibs(sysroot)

    baseline_cross_check: dict[str, Any] | None = None
    if baseline_json and Path(baseline_json).is_file():
        bdata = json.loads(Path(baseline_json).read_text(encoding="utf-8"))
        bcensus = bdata["sysroot_rlib_census"]
        live_stems = {k.split("-", 1)[0]: v for k, v in census_live["relaxable_by_rlib"].items()}
        base_stems = {k.split("-", 1)[0]: v for k, v in bcensus["relaxable_by_rlib"].items()}
        baseline_cross_check = {
            "baseline_rustc_version": bdata["rustc_version"].splitlines()[0],
            "baseline_rlib_count": bcensus["rlib_count"],
            "baseline_total_relocations": bcensus["total_relocations"],
            "baseline_by_type": bcensus["by_type"],
            "baseline_opcode_relaxable_total": bcensus["opcode_relaxable_total"],
            "baseline_relaxable_by_rlib": bcensus["relaxable_by_rlib"],
            "same_rlib_count": census_live["rlib_count"] == bcensus["rlib_count"],
            "same_10_reloc_types": set(census_live["by_type"]) == set(bcensus["by_type"]),
            "same_6_relaxable_crate_stems": set(live_stems) == set(base_stems),
            "profiler_builtins_rex_gotpcrelx_match": (
                live_stems.get("libprofiler_builtins", {}).get("R_X86_64_REX_GOTPCRELX")
                == base_stems.get("libprofiler_builtins", {}).get("R_X86_64_REX_GOTPCRELX")
            ),
        }

    obj_disasm: dict[str, Any] = {}
    obj_relocs: dict[str, Any] = {}
    linked_matrix: dict[str, Any] = {}
    nostd_matrix: dict[str, Any] = {}

    with tempfile.TemporaryDirectory() as td_str:
        td = Path(td_str)
        # 1. Separate rlib objects so LLVM does not pre-fold dso_local TLS/GOT accesses
        tls_specs = [
            ("global-dynamic", "tls_gd", "get_tls_gd"),
            ("local-dynamic", "tls_ld", "get_tls_ld"),
            ("initial-exec", "tls_ie", "get_tls_ie"),
        ]
        for model, modname, fnname in tls_specs:
            rs = td / f"{modname}.rs"
            extra_ie_asm = ""
            extra_ie_call = ""
            if model == "initial-exec":
                extra_ie_asm = f'''
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn {fnname}_r12_asm() -> u64 {{
    let off: i64;
    unsafe {{
        core::arch::asm!(
            "mov r12, qword ptr fs:[0]",
            "add r12, qword ptr [rip + {{sym}}@GOTTPOFF]",
            "mov {{out}}, qword ptr [r12]",
            sym = sym TLS_{modname.upper()},
            out = out(reg) off,
            out("r12") _,
        );
    }}
    off as u64
}}
'''
            rs.write_text(
                f'''#![feature(thread_local)]
#![crate_type = "rlib"]
#[thread_local]
pub static mut TLS_{modname.upper()}: u64 = 77;

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn {fnname}() -> u64 {{
    unsafe {{ core::ptr::read_volatile(&raw const TLS_{modname.upper()}) }}
}}

#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn {fnname}_addr() -> usize {{
    (&raw const TLS_{modname.upper()}) as usize
}}
{extra_ie_asm}
''',
                encoding="utf-8",
            )
            subprocess.check_call(
                [
                    "rustc",
                    "-O",
                    "-C",
                    "codegen-units=1",
                    "-Z",
                    f"tls-model={model}",
                    "--emit=obj,link",
                    "--out-dir",
                    str(td),
                    str(rs),
                ],
                stderr=subprocess.DEVNULL,
            )
            obj = td / f"{modname}.o"
            fns = [fnname, f"{fnname}_addr"] + ([f"{fnname}_r12_asm"] if model == "initial-exec" else [])
            obj_disasm[modname] = parse_objdump_function(obj, fns, with_relocs=True)
            obj_relocs[modname] = parse_dynamic_relocs(obj)

        for tag, zflag in [("strict", "no"), ("relaxable", "yes")]:
            rs = td / f"got_{tag}.rs"
            rs.write_text(
                f'''#![crate_type = "rlib"]
unsafe extern "C" {{
    static EXT_VAL_{tag.upper()}: u64;
    fn ext_callee_{tag}(x: u64) -> u64;
}}
#[unsafe(no_mangle)]
#[inline(never)]
pub unsafe extern "C" fn use_got_{tag}() -> u64 {{
    let p = &raw const EXT_VAL_{tag.upper()};
    let r = unsafe {{ ext_callee_{tag}(p as usize as u64) }};
    r.wrapping_add(unsafe {{ core::ptr::read_volatile(p) }})
}}
''',
                encoding="utf-8",
            )
            subprocess.check_call(
                [
                    "rustc",
                    "-O",
                    "-C",
                    "codegen-units=1",
                    "-Z",
                    f"relax-elf-relocations={zflag}",
                    "--emit=obj,link",
                    "--out-dir",
                    str(td),
                    str(rs),
                ],
                stderr=subprocess.DEVNULL,
            )
            obj = td / f"got_{tag}.o"
            obj_disasm[f"got_{tag}"] = parse_objdump_function(obj, [f"use_got_{tag}"], with_relocs=True)
            obj_relocs[f"got_{tag}"] = parse_dynamic_relocs(obj)

        # Driver crate with backward PC-relative reference, Drop + catch_unwind DWARF CFI exercise
        drv = td / "drv.rs"
        drv.write_text(
            '''extern crate tls_gd;
extern crate tls_ld;
extern crate tls_ie;
extern crate got_strict;
extern crate got_relaxable;

use std::sync::atomic::{AtomicU64, Ordering};

#[unsafe(no_mangle)]
pub static EXT_VAL_STRICT: u64 = 10;
#[unsafe(no_mangle)]
pub static EXT_VAL_RELAXABLE: u64 = 20;
static DROP_OBS: AtomicU64 = AtomicU64::new(0);

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ext_callee_strict(x: u64) -> u64 { x & 1 }

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn ext_callee_relaxable(x: u64) -> u64 { x & 1 }

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn backward_leaf(x: u64) -> u64 {
    core::hint::black_box(x).wrapping_add(5)
}

#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C-unwind" fn forward_unwinding_caller(do_panic: bool) -> u64 {
    struct Guard<'a>(&'a AtomicU64);
    impl<'a> Drop for Guard<'a> {
        #[inline(never)]
        fn drop(&mut self) {
            self.0.fetch_add(1, Ordering::SeqCst);
        }
    }
    let _g = Guard(&DROP_OBS);
    let f: extern "C" fn(u64) -> u64 = core::hint::black_box(backward_leaf);
    let val = f(3);
    if do_panic {
        panic!("unwind check {}", val);
    }
    val
}

#[unsafe(no_mangle)]
pub extern "C" fn exported_api() -> u64 {
    unsafe {
        tls_gd::get_tls_gd() + (tls_gd::get_tls_gd_addr() & 1) as u64
        + tls_ld::get_tls_ld() + (tls_ld::get_tls_ld_addr() & 1) as u64
        + tls_ie::get_tls_ie() + (tls_ie::get_tls_ie_addr() & 1) as u64
        + tls_ie::get_tls_ie_r12_asm()
        + got_strict::use_got_strict() + got_relaxable::use_got_relaxable()
        + forward_unwinding_caller(false)
    }
}

#[cfg(not(feature = "cdylib_mode"))]
fn main() {
    let base = exported_api();
    let res = std::panic::catch_unwind(|| forward_unwinding_caller(true));
    assert!(res.is_err());
    assert_eq!(DROP_OBS.load(Ordering::SeqCst), 2);
    assert!(base >= 346);
    std::process::exit(0);
}
''',
            encoding="utf-8",
        )
        r_drv = subprocess.run(
            [
                "rustc",
                "-O",
                "-C",
                "codegen-units=1",
                "--emit=obj",
                "-L",
                str(td),
                str(drv),
                "-o",
                str(td / "drv.o"),
            ],
            text=True,
            capture_output=True,
        )
        if r_drv.returncode != 0:
            raise RuntimeError(f"drv.rs obj compile failed:\n{r_drv.stderr}")
        obj_disasm["drv"] = parse_objdump_function(
            td / "drv.o", ["backward_leaf", "forward_unwinding_caller"], with_relocs=True
        )
        obj_relocs["drv"] = parse_dynamic_relocs(td / "drv.o")

        gnu_ld_flags = ["-Z", "unstable-options", "-C", "linker-flavor=gnu-cc", "-C", "link-self-contained=-linker"]
        rust_lld_flags = ["-Z", "unstable-options", "-C", "linker-flavor=gnu-lld-cc", "-C", "link-self-contained=+linker"]

        probe_fns = [
            "get_tls_gd",
            "get_tls_gd_addr",
            "get_tls_ld",
            "get_tls_ld_addr",
            "get_tls_ie",
            "get_tls_ie_addr",
            "get_tls_ie_r12_asm",
            "use_got_strict",
            "use_got_relaxable",
            "backward_leaf",
            "forward_unwinding_caller",
        ]

        configs = [
            ("dyn_pie_gnu_ld", "gnu_ld", "dyn_pie", gnu_ld_flags, True),
            ("dyn_pie_rust_lld", "rust_lld", "dyn_pie", rust_lld_flags, True),
            ("dyn_pie_norelax_gnu_ld", "gnu_ld", "dyn_pie_norelax", gnu_ld_flags + ["-C", "link-arg=-Wl,--no-relax"], True),
            ("dyn_pie_norelax_rust_lld", "rust_lld", "dyn_pie_norelax", rust_lld_flags + ["-C", "link-arg=-Wl,--no-relax"], True),
            ("static_pie_gnu_ld", "gnu_ld", "static_pie", gnu_ld_flags + ["-C", "target-feature=+crt-static", "-C", "relocation-model=pic"], True),
            ("static_pie_rust_lld", "rust_lld", "static_pie", rust_lld_flags + ["-C", "target-feature=+crt-static", "-C", "relocation-model=pic"], True),
            ("cdylib_gnu_ld", "gnu_ld", "cdylib", gnu_ld_flags + ["--crate-type=cdylib", "--cfg", 'feature="cdylib_mode"'], False),
            ("cdylib_rust_lld", "rust_lld", "cdylib", rust_lld_flags + ["--crate-type=cdylib", "--cfg", 'feature="cdylib_mode"'], False),
        ]

        for cname, linker_kind, mode_kind, extra_flags, is_exec in configs:
            out_bin = td / cname
            link_res = run_timed(
                ["rustc", "-O", "-C", "codegen-units=1", "-L", str(td), str(drv), "-o", str(out_bin)]
                + extra_flags
            )
            if link_res["rc"] != 0:
                raise RuntimeError(f"Link failed for {cname}: {link_res['stderr']}")
            exec_res = run_timed([str(out_bin)]) if is_exec else None
            if exec_res is not None and exec_res["rc"] != 0:
                raise RuntimeError(f"Execution failed for {cname}: rc={exec_res['rc']} err={exec_res['stderr']}")
            comment_out = subprocess.check_output(["readelf", "-p", ".comment", str(out_bin)], text=True)
            linked_matrix[cname] = {
                "linker_kind": linker_kind,
                "mode_kind": mode_kind,
                "link_elapsed_sec": link_res["elapsed_sec"],
                "exec_rc": exec_res["rc"] if exec_res is not None else None,
                "has_lld_comment": "LLD" in comment_out,
                "binary_size_bytes": out_bin.stat().st_size,
                "dynamic_reloc_totals": parse_dynamic_relocs(out_bin),
                "padding_distribution": count_text_padding_distribution(out_bin),
                "elf_and_eh_frame": read_elf64_sections_and_verify_eh_frame_hdr(out_bin),
                "functions": parse_objdump_function(out_bin, probe_fns, with_relocs=False),
            }

        # 2. Freestanding #![no_std] #![no_main] -nostdlib -static-pie survival probe
        nostd_rs = td / "nostd_static_pie.rs"
        nostd_rs.write_text(
            '''#![no_std]
#![no_main]
use core::panic::PanicInfo;
#[panic_handler]
fn panic(_: &PanicInfo) -> ! { loop {} }
#[unsafe(no_mangle)]
pub static GLOBAL_CONST: u64 = 42;
#[unsafe(no_mangle)]
#[inline(never)]
pub extern "C" fn helper(x: u64) -> u64 {
    core::hint::black_box(x) + unsafe { core::ptr::read_volatile(&GLOBAL_CONST) }
}
#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    let code = helper(0) - 42;
    unsafe {
        core::arch::asm!(
            "mov rax, 60",
            "syscall",
            in("rdi") code,
            options(noreturn)
        );
    }
}
''',
            encoding="utf-8",
        )
        for zmode, zflags in [("default_gotpcrel", ["-Z", "relax-elf-relocations=no"]), ("relax_elf_relocs_yes", ["-Z", "relax-elf-relocations=yes"])]:
            subprocess.check_call(
                ["rustc", "-O", "-C", "panic=abort", "-C", "relocation-model=pic", "--emit=obj", str(nostd_rs), "-o", str(td / f"nostd_{zmode}.o")] + zflags
            )
            nostd_obj_fns = parse_objdump_function(td / f"nostd_{zmode}.o", ["helper"], with_relocs=True)
            for linker_kind, lflags in [("gnu_ld", gnu_ld_flags), ("rust_lld", rust_lld_flags)]:
                cname = f"nostd_{zmode}_{linker_kind}"
                out_bin = td / cname
                subprocess.check_call(
                    [
                        "rustc",
                        "-O",
                        "-C",
                        "panic=abort",
                        "-C",
                        "relocation-model=pic",
                        "-C",
                        "link-arg=-nostdlib",
                        "-C",
                        "link-arg=-static-pie",
                        str(nostd_rs),
                        "-o",
                        str(out_bin),
                    ]
                    + zflags
                    + lflags
                )
                rc_exec = subprocess.run([str(out_bin)]).returncode
                nostd_matrix[cname] = {
                    "linker_kind": linker_kind,
                    "relax_flag": zmode,
                    "exec_rc": rc_exec,
                    "signal_name": "SIGSEGV" if rc_exec == -11 else ("EXIT_OK" if rc_exec == 0 else str(rc_exec)),
                    "dynamic_reloc_totals": parse_dynamic_relocs(out_bin),
                    "obj_helper": nostd_obj_fns.get("helper", {}),
                    "linked_helper": parse_objdump_function(out_bin, ["helper"], with_relocs=False).get("helper", {}),
                }

    payload = {
        "probe_name": "elf64_postlink_relocation_tls_relaxation_and_ehframe",
        "observed_at": time.strftime("%Y-%m-%d", time.gmtime()),
        "rustc_version": sanitize_text(rustc_ver, home_dir, sysroot),
        "gnu_ld_version": gnu_ld_ver,
        "rust_lld_version": lld_ver,
        "sysroot_rlib_census_live": census_live,
        "sysroot_rlib_census_cross_check": baseline_cross_check,
        "pre_link_objects": {
            "reloc_totals": obj_relocs,
            "functions": obj_disasm,
        },
        "linked_configs": linked_matrix,
        "nostd_static_pie_matrix": nostd_matrix,
    }
    return payload


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=str(Path(__file__).resolve().parent / "elf64_postlink_probe_results.json"),
        help="Output JSON artifact path",
    )
    parser.add_argument(
        "--baseline-json",
        default=None,
        help="Optional prior rustc 1.102.0-nightly census JSON for cross-checking",
    )
    args = parser.parse_args()
    os.environ["PATH"] = os.path.expanduser("~/.cargo/bin") + ":" + os.environ["PATH"]
    data = run_probes(args.baseline_json)
    out_path = Path(args.out)
    out_path.write_text(json.dumps(data, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out_path} ({len(data['linked_configs'])} std configs, {len(data['nostd_static_pie_matrix'])} no_std configs)")
    print(
        f"sysroot live census: {data['sysroot_rlib_census_live']['rlib_count']} rlibs, "
        f"{data['sysroot_rlib_census_live']['total_relocations']} relocs, "
        f"{data['sysroot_rlib_census_live']['opcode_relaxable_total']} relaxable"
    )
    for cname, cfg in data["linked_configs"].items():
        eh = cfg["elf_and_eh_frame"]["eh_frame_hdr"]
        print(
            f"  {cname:26s}: lld={str(cfg['has_lld_comment']):5s} rc={str(cfg['exec_rc']):4s} "
            f"fdes={eh['fde_count']:3d} sorted={eh['strictly_sorted_pc']} mismatch={eh['fde_pc_mismatches']} "
            f"int3={cfg['padding_distribution']['int3_insns']} nop={cfg['padding_distribution']['nop_insns']}"
        )
    for cname, cfg in data["nostd_static_pie_matrix"].items():
        print(f"  {cname:34s}: exec_rc={cfg['exec_rc']} ({cfg['signal_name']}) relocs={cfg['dynamic_reloc_totals']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
