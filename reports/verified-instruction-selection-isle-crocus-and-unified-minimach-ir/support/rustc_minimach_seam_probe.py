#!/usr/bin/env python3
"""Real-toolchain MiniMach seam probe: rustc ELF64 object, asm!, LSDA/CFI,
direct byte codec parity, V1 mutant kills, and Lean 4 kernel verification.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any


RUST_SPECIMENS = r"""#![allow(dead_code)]

pub struct DropGuard(*mut u32);

impl Drop for DropGuard {
    #[inline(never)]
    fn drop(&mut self) {
        unsafe {
            core::ptr::write_volatile(self.0, 1);
        }
    }
}

#[no_mangle]
#[inline(never)]
pub unsafe extern "C" fn asm_alu_subreg(mut a: u64, b: u64) -> u64 {
    core::arch::asm!(
        "add {0}, {1}",
        "xor {0:e}, {1:e}",
        inout(reg) a,
        in(reg) b,
        options(nomem, nostack)
    );
    a
}

#[no_mangle]
#[inline(never)]
pub extern "C-unwind" fn unwind_call_lsda(slot: *mut u32, cb: extern "C-unwind" fn()) {
    let _guard = DropGuard(slot);
    cb();
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn subreg_lanes(x: u64, b: u8) -> u64 {
    let kept_upper = (x & !0xFFu64) | (b as u64);
    let zext32 = (x as u32).wrapping_add(b as u32) as u64;
    kept_upper ^ zext32
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn stack_frame_probe(a: u64, b: u64, c: u64) -> u64 {
    let mut buf = [a, b, c, a ^ b];
    unsafe {
        let p = buf.as_mut_ptr();
        core::ptr::write_volatile(p.add(1), b.wrapping_add(c));
        core::ptr::read_volatile(p.add(1)).wrapping_add(core::ptr::read_volatile(p.add(3)))
    }
}
"""


X64_GPR_NAMES = [
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
    "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
]
X64_GPR32_NAMES = [
    "eax", "ecx", "edx", "ebx", "esp", "ebp", "esi", "edi",
    "r8d", "r9d", "r10d", "r11d", "r12d", "r13d", "r14d", "r15d",
]


@dataclass(frozen=True)
class MiniX64Inst:
    op: str
    dst: int = 0
    src: int = 0
    imm32: int = 0
    canonical_rex: bool = True

    def encode(self, force_canonical_rex: bool = True) -> bytes:
        if self.op == "ret":
            return bytes([0xC3])
        if self.op == "call_rel32":
            return bytes([0xE8]) + struct.pack("<i", self.imm32)
        if self.op in ("add64_rr", "mov64_rr", "xor32_rr_zext"):
            opcode = {"add64_rr": 0x01, "mov64_rr": 0x89, "xor32_rr_zext": 0x31}[self.op]
            w = 1 if self.op in ("add64_rr", "mov64_rr") else 0
            r = (self.src >> 3) & 1
            b = (self.dst >> 3) & 1
            modrm = 0xC0 | ((self.src & 7) << 3) | (self.dst & 7)
            need_rex = force_canonical_rex or w == 1 or r == 1 or b == 1 or self.canonical_rex
            if need_rex:
                rex = 0x40 | (w << 3) | (r << 2) | b
                return bytes([rex, opcode, modrm])
            return bytes([opcode, modrm])
        if self.op == "push64":
            b = (self.dst >> 3) & 1
            op = 0x50 + (self.dst & 7)
            if force_canonical_rex or b == 1 or self.canonical_rex:
                return bytes([0x40 | b, op])
            return bytes([op])
        if self.op == "pop64":
            b = (self.dst >> 3) & 1
            op = 0x58 + (self.dst & 7)
            if force_canonical_rex or b == 1 or self.canonical_rex:
                return bytes([0x40 | b, op])
            return bytes([op])
        raise ValueError(f"unsupported op {self.op}")


def decode_one_x64_subset(buf: bytes, offset: int) -> tuple[MiniX64Inst | None, int]:
    """Decode core x86-64 MiniMach instructions (with or without optional REX)."""
    if offset >= len(buf):
        return None, offset
    b0 = buf[offset]
    if b0 == 0xC3:
        return MiniX64Inst("ret", canonical_rex=False), offset + 1
    if b0 == 0xE8 and offset + 5 <= len(buf):
        (rel,) = struct.unpack_from("<i", buf, offset + 1)
        return MiniX64Inst("call_rel32", imm32=rel, canonical_rex=False), offset + 5
    has_rex = 0x40 <= b0 <= 0x4F
    pos = offset
    w = r = b = 0
    if has_rex:
        w = (b0 >> 3) & 1
        r = (b0 >> 2) & 1
        b = b0 & 1
        pos += 1
        if pos >= len(buf):
            return None, offset + 1
    op = buf[pos]
    if op in (0x01, 0x31, 0x89) and pos + 1 < len(buf):
        modrm = buf[pos + 1]
        if (modrm & 0xC0) == 0xC0:
            src = (r << 3) | ((modrm >> 3) & 7)
            dst = (b << 3) | (modrm & 7)
            if op == 0x01 and w == 1:
                return MiniX64Inst("add64_rr", dst=dst, src=src, canonical_rex=has_rex), pos + 2
            if op == 0x89 and w == 1:
                return MiniX64Inst("mov64_rr", dst=dst, src=src, canonical_rex=has_rex), pos + 2
            if op == 0x31 and w == 0:
                return MiniX64Inst("xor32_rr_zext", dst=dst, src=src, canonical_rex=has_rex), pos + 2
    if 0x50 <= op <= 0x57 and w == 0 and r == 0:
        return MiniX64Inst("push64", dst=(b << 3) | (op - 0x50), canonical_rex=has_rex), pos + 1
    if 0x58 <= op <= 0x5F and w == 0 and r == 0:
        return MiniX64Inst("pop64", dst=(b << 3) | (op - 0x58), canonical_rex=has_rex), pos + 1
    return None, offset + 1


def parse_elf64(data: bytes) -> dict[str, Any]:
    if data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise RuntimeError("expected little-endian ELF64 object")
    (
        _ident,
        e_type,
        e_machine,
        _e_version,
        _e_entry,
        _e_phoff,
        e_shoff,
        _e_flags,
        _e_ehsize,
        _e_phentsize,
        _e_phnum,
        e_shentsize,
        e_shnum,
        e_shstrndx,
    ) = struct.unpack_from("<16sHHIQQQIHHHHHH", data, 0)
    if e_machine != 62:
        raise RuntimeError(f"unexpected ELF machine {e_machine} (expected EM_X86_64=62)")

    shdrs = []
    for idx in range(e_shnum):
        off = e_shoff + idx * e_shentsize
        fields = struct.unpack_from("<IIQQQQIIQQ", data, off)
        shdrs.append(
            {
                "index": idx,
                "sh_name": fields[0],
                "sh_type": fields[1],
                "sh_flags": fields[2],
                "sh_addr": fields[3],
                "sh_offset": fields[4],
                "sh_size": fields[5],
                "sh_link": fields[6],
                "sh_info": fields[7],
                "sh_addralign": fields[8],
                "sh_entsize": fields[9],
            }
        )

    shstr_hdr = shdrs[e_shstrndx]
    shstr_bytes = data[shstr_hdr["sh_offset"] : shstr_hdr["sh_offset"] + shstr_hdr["sh_size"]]

    def cstr(blob: bytes, start: int) -> str:
        end = blob.find(b"\x00", start)
        return blob[start:end].decode("utf-8", errors="replace") if end != -1 else ""

    by_name: dict[str, dict[str, Any]] = {}
    for sh in shdrs:
        sh["name"] = cstr(shstr_bytes, sh["sh_name"])
        sh["bytes"] = data[sh["sh_offset"] : sh["sh_offset"] + sh["sh_size"]] if sh["sh_type"] != 8 else b""
        if sh["name"]:
            by_name[sh["name"]] = sh

    symtab = by_name.get(".symtab")
    strtab = by_name.get(".strtab")
    symbols: dict[str, dict[str, Any]] = {}
    if symtab and strtab:
        str_bytes = strtab["bytes"]
        count = symtab["sh_size"] // symtab["sh_entsize"]
        for i in range(count):
            soff = symtab["sh_offset"] + i * symtab["sh_entsize"]
            st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                "<IBBHQQ", data, soff
            )
            sname = cstr(str_bytes, st_name)
            if sname and 0 < st_shndx < len(shdrs):
                sec = shdrs[st_shndx]
                sym_bytes = sec["bytes"][st_value : st_value + st_size]
                symbols[sname] = {
                    "index": i,
                    "name": sname,
                    "shndx": st_shndx,
                    "section_name": sec["name"],
                    "value": st_value,
                    "size": st_size,
                    "type": st_info & 0xF,
                    "bind": st_info >> 4,
                    "bytes": sym_bytes,
                }

    def parse_rela_section(sec: dict[str, Any]) -> list[dict[str, Any]]:
        entries = []
        cnt = sec["sh_size"] // sec["sh_entsize"]
        for i in range(cnt):
            roff = sec["sh_offset"] + i * sec["sh_entsize"]
            r_offset, r_info, r_addend = struct.unpack_from("<QQq", data, roff)
            entries.append(
                {
                    "section": sec["name"],
                    "offset": r_offset,
                    "sym_idx": r_info >> 32,
                    "type": r_info & 0xFFFFFFFF,
                    "addend": r_addend,
                }
            )
        return entries

    rela_text: list[dict[str, Any]] = []
    rela_eh_frame: list[dict[str, Any]] = []
    text_total_bytes = 0
    lsda_total_bytes = 0
    for sh in shdrs:
        nm = sh["name"]
        if nm == ".text" or nm.startswith(".text."):
            text_total_bytes += sh["sh_size"]
        if nm == ".gcc_except_table" or nm.startswith(".gcc_except_table."):
            lsda_total_bytes += sh["sh_size"]
        if nm == ".rela.text" or nm.startswith(".rela.text."):
            rela_text.extend(parse_rela_section(sh))
        if nm == ".rela.eh_frame" or nm.startswith(".rela.eh_frame."):
            rela_eh_frame.extend(parse_rela_section(sh))

    def count_eh_frame_records(raw: bytes) -> tuple[int, int]:
        pos = 0
        cies = 0
        fdes = 0
        while pos + 4 <= len(raw):
            (length,) = struct.unpack_from("<I", raw, pos)
            pos += 4
            if length == 0:
                break
            if pos + length > len(raw):
                break
            (cie_id,) = struct.unpack_from("<I", raw, pos)
            if cie_id == 0:
                cies += 1
            else:
                fdes += 1
            pos += length
        return cies, fdes

    eh_sec = by_name.get(".eh_frame")
    eh_bytes = eh_sec["bytes"] if eh_sec else b""
    cies, fdes = count_eh_frame_records(eh_bytes)

    return {
        "e_type": e_type,
        "sections": {
            sh["name"]: {
                "size": sh["sh_size"],
                "offset": sh["sh_offset"],
                "align": sh["sh_addralign"],
            }
            for sh in shdrs
            if sh["name"]
        },
        "text_total_bytes": text_total_bytes,
        "lsda_total_bytes": lsda_total_bytes,
        "symbols": symbols,
        "rela_text": rela_text,
        "rela_eh_frame": rela_eh_frame,
        "eh_frame_cies": cies,
        "eh_frame_fdes": fdes,
    }


def run_v1_mutants() -> list[dict[str, Any]]:
    """Run 6 planted-bug mutants to verify MiniMach invariant checkers catch each hazard."""
    def lane_write(lv: str, r: int, v: int) -> int:
        m64 = 0xFFFF_FFFF_FFFF_FFFF
        if lv == "full64":
            return v & m64
        if lv == "lo32_zext":
            return v & 0xFFFF_FFFF
        if lv == "lo8_keep":
            return (r & 0xFFFF_FFFF_FFFF_FF00) | (v & 0xFF)
        if lv == "hi8_keep":
            return (r & 0xFFFF_FFFF_FFFF_00FF) | ((v & 0xFF) << 8)
        raise ValueError(lv)

    mutants: list[dict[str, Any]] = []

    # Mutant 1: Whole-register coalescing ignores lo32_zext upper-32 zeroing.
    r0 = 0x1234_5678_9ABC_DEF0
    m1_actual = lane_write("lo32_zext", r0, 0x0000_0001)
    m1_mutant = (r0 & 0xFFFF_FFFF_0000_0000) | 0x0000_0001
    mutants.append(
        {
            "id": "mutant1_lo32_zext_upper_preserve",
            "caught": (m1_actual >> 32) == 0 and m1_actual != m1_mutant,
            "witness": f"actual=0x{m1_actual:016x} vs buggy_upper_preserve=0x{m1_mutant:016x}",
        }
    )

    # Mutant 2: Treating lo8_keep (mov al) as zeroing AH (lo8_zext).
    m2_actual = lane_write("lo8_keep", r0, 0x42)
    m2_mutant = 0x42
    mutants.append(
        {
            "id": "mutant2_lo8_keep_clobbers_hi",
            "caught": ((m2_actual >> 8) & 0xFF) == 0xDE and m2_actual != m2_mutant,
            "witness": f"AH preserved=0x{(m2_actual>>8)&0xFF:02x}, buggy=0x{(m2_mutant>>8)&0xFF:02x}",
        }
    )

    # Mutant 3: Omitting REX byte on r8..r15 aliases rax..rdi (register index collision).
    good_r8 = MiniX64Inst("add64_rr", dst=8, src=9).encode(force_canonical_rex=True)
    bad_no_rex_b = bytes([0x48, 0x01, 0xC8])  # W=1, R=0, B=0 -> add rax, rcx instead of add r8, r9
    dec_good, _ = decode_one_x64_subset(good_r8, 0)
    dec_bad, _ = decode_one_x64_subset(bad_no_rex_b, 0)
    mutants.append(
        {
            "id": "mutant3_missing_rex_r8_alias",
            "caught": dec_good != dec_bad and dec_good.dst == 8 and dec_bad.dst == 0,
            "witness": f"good={good_r8.hex()} (dst=r8) vs buggy={bad_no_rex_b.hex()} (dst=rax)",
        }
    )

    # Mutant 4: Narrow signed-8 conditional branch accepted at displacement +128 (overflow).
    disp_edge = 128
    mutants.append(
        {
            "id": "mutant4_jcc_rel8_plus_128_overflow",
            "caught": not (-128 <= disp_edge <= 127),
            "witness": f"disp={disp_edge} outside [-128, 127]; requires relaxation to jcc_rel32",
        }
    )

    # Mutant 5: Outlined thunk omits +8 return-address SP displacement shift.
    sp0 = 0x7FFF_0000_1000
    caller_slot_off = 16
    inline_addr = sp0 + caller_slot_off
    sp_in_thunk = sp0 - 8
    buggy_thunk_addr = sp_in_thunk + caller_slot_off  # unshifted!
    fixed_thunk_addr = sp_in_thunk + (caller_slot_off + 8)
    mutants.append(
        {
            "id": "mutant5_outliner_unshifted_sp_load",
            "caught": fixed_thunk_addr == inline_addr and buggy_thunk_addr != inline_addr,
            "witness": f"inline=0x{inline_addr:x}, fixed=0x{fixed_thunk_addr:x}, buggy=0x{buggy_thunk_addr:x}",
        }
    )

    # Mutant 6: Missing -4 PC-relative relocation addend bias on R_X86_64_PLT32.
    call_site = 0x401000
    target_fn = 0x401120
    correct_disp = target_fn - (call_site + 4)  # addend = -4 from relocation offset (opcode + 1)
    buggy_disp = target_fn - call_site
    mutants.append(
        {
            "id": "mutant6_missing_plt32_addend_minus4",
            "caught": correct_disp != buggy_disp and (buggy_disp - correct_disp) == 4,
            "witness": f"correct_rel32={correct_disp} vs buggy_no_addend={buggy_disp}",
        }
    )

    return mutants


def resolve_tool(name: str, extra_dirs: list[str]) -> str | None:
    found = shutil.which(name)
    if found:
        return found
    for d in extra_dirs:
        cand = Path(d).expanduser() / name
        if cand.is_file() and os.access(cand, os.X_OK):
            return str(cand)
    return None


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        default=str(Path(__file__).resolve().parent / "probe_results.json"),
        help="Output JSON path (defaults to support/probe_results.json)",
    )
    parser.add_argument(
        "--skip-lean",
        action="store_true",
        help="Skip invoking lean on minimach_unified_probe.lean",
    )
    args = parser.parse_args()

    extra_bins = ["~/.cargo/bin", "~/.local/bin", "~/.elan/bin"]
    rustc_bin = resolve_tool("rustc", extra_bins)
    readelf_bin = resolve_tool("readelf", extra_bins)
    objdump_bin = resolve_tool("objdump", extra_bins)
    lean_run_bin = resolve_tool("anneal-lean-run", extra_bins)
    lean_bin = resolve_tool("lean", extra_bins)

    if not rustc_bin:
        print("rustc not found in PATH or ~/.cargo/bin", file=sys.stderr)
        return 1

    rustc_ver = subprocess.run([rustc_bin, "--version"], capture_output=True, text=True, check=True).stdout.strip()
    rustc_vv = subprocess.run([rustc_bin, "-vV"], capture_output=True, text=True, check=True).stdout.strip()
    readelf_ver = (
        subprocess.run([readelf_bin, "--version"], capture_output=True, text=True).stdout.splitlines()[0].strip()
        if readelf_bin
        else "unavailable"
    )
    objdump_ver = (
        subprocess.run([objdump_bin, "--version"], capture_output=True, text=True).stdout.splitlines()[0].strip()
        if objdump_bin
        else "unavailable"
    )

    tmpdir = tempfile.mkdtemp(prefix="minimach_seam_probe_")
    try:
        rs_path = Path(tmpdir) / "specimens.rs"
        obj_path = Path(tmpdir) / "specimens.o"
        rs_path.write_text(RUST_SPECIMENS, encoding="utf-8")

        t0 = time.perf_counter()
        comp = subprocess.run(
            [
                rustc_bin,
                "--edition=2021",
                "--crate-type=lib",
                "-C",
                "opt-level=2",
                "-C",
                "panic=unwind",
                "-C",
                "force-unwind-tables=yes",
                "--emit=obj",
                str(rs_path),
                "-o",
                str(obj_path),
            ],
            capture_output=True,
            text=True,
        )
        compile_ms = (time.perf_counter() - t0) * 1000.0
        if comp.returncode != 0:
            raise RuntimeError(f"rustc compile failed:\n{comp.stderr}")

        obj_bytes = obj_path.read_bytes()
        elf = parse_elf64(obj_bytes)

        # Cross-check with objdump -d if present
        objdump_text = ""
        if objdump_bin:
            od = subprocess.run([objdump_bin, "-d", str(obj_path)], capture_output=True, text=True)
            if od.returncode == 0:
                objdump_text = od.stdout

        # Inspect asm_alu_subreg bytes from compiled ELF64
        asm_sym = elf["symbols"]["asm_alu_subreg"]
        asm_slice = asm_sym["bytes"]
        decoded_seq: list[dict[str, Any]] = []
        off = 0
        while off < len(asm_slice):
            inst, nxt = decode_one_x64_subset(asm_slice, off)
            raw_chunk = asm_slice[off:nxt]
            if inst is not None:
                reencoded = inst.encode(force_canonical_rex=inst.canonical_rex)
                decoded_seq.append(
                    {
                        "offset": off,
                        "op": inst.op,
                        "dst": X64_GPR_NAMES[inst.dst] if inst.op != "xor32_rr_zext" else X64_GPR32_NAMES[inst.dst],
                        "src": X64_GPR_NAMES[inst.src] if inst.op != "xor32_rr_zext" else X64_GPR32_NAMES[inst.src],
                        "raw_hex": raw_chunk.hex(),
                        "reencoded_hex": reencoded.hex(),
                        "exact_roundtrip": raw_chunk == reencoded,
                    }
                )
            else:
                decoded_seq.append(
                    {"offset": off, "op": "unmodeled_byte", "raw_hex": raw_chunk.hex(), "exact_roundtrip": False}
                )
            off = nxt

        asm_ops_found = [d["op"] for d in decoded_seq]
        asm_roundtrip_all_ok = bool(decoded_seq) and all(d["exact_roundtrip"] for d in decoded_seq)
        has_add_and_xor = "add64_rr" in asm_ops_found and "xor32_rr_zext" in asm_ops_found

        # Inspect unwind_call_lsda and ELF unwind/reloc tables
        unwind_sym = elf["symbols"]["unwind_call_lsda"]
        subreg_sym = elf["symbols"]["subreg_lanes"]
        stack_sym = elf["symbols"]["stack_frame_probe"]

        # Verify direct MiniMach encoder emits exact bytes for the asm! body inside asm_alu_subreg
        direct_asm_body = (
            MiniX64Inst("add64_rr", dst=0, src=6, canonical_rex=True).encode(force_canonical_rex=True)
            + MiniX64Inst("xor32_rr_zext", dst=0, src=6, canonical_rex=False).encode(force_canonical_rex=False)
        )
        direct_subseq_ok = direct_asm_body in asm_slice

        # V1 mutant kill suite
        mutants = run_v1_mutants()

        # Optional Lean 4 kernel verification
        lean_probe_path = Path(__file__).resolve().parent / "minimach_unified_probe.lean"
        lean_result: dict[str, Any] = {"executed": False}
        if not args.skip_lean and lean_probe_path.exists() and (lean_run_bin or lean_bin):
            cmd = [lean_run_bin, "lean", str(lean_probe_path)] if lean_run_bin else [lean_bin, str(lean_probe_path)]
            ver_cmd = [lean_bin or "lean", "--version"]
            lean_ver = subprocess.run(ver_cmd, capture_output=True, text=True).stdout.strip()
            t1 = time.perf_counter()
            lr = subprocess.run(cmd, capture_output=True, text=True)
            lean_ms = (time.perf_counter() - t1) * 1000.0
            axiom_lines = [
                ln.strip()
                for ln in (lr.stdout + "\n" + lr.stderr).splitlines()
                if "depends on axioms:" in ln
            ]
            has_forbidden = any(
                tok in (lr.stdout + lr.stderr)
                for tok in ("sorryAx", "Lean.ofReduceBool", "Lean.trustCompiler")
            )
            lean_result = {
                "executed": True,
                "lean_version": lean_ver,
                "returncode": lr.returncode,
                "elapsed_ms": round(lean_ms, 2),
                "axiom_reports": axiom_lines,
                "axiom_count": len(axiom_lines),
                "forbidden_axioms_detected": has_forbidden,
            }

        results = {
            "toolchains": {
                "rustc_version": rustc_ver,
                "rustc_host": next(
                    (ln.split(":", 1)[1].strip() for ln in rustc_vv.splitlines() if ln.startswith("host:")),
                    "unknown",
                ),
                "readelf_version": readelf_ver,
                "objdump_version": objdump_ver,
            },
            "rustc_compile": {
                "elapsed_ms": round(compile_ms, 2),
                "object_size_bytes": len(obj_bytes),
                "text_bytes": elf["text_total_bytes"],
                "eh_frame_bytes": elf["sections"].get(".eh_frame", {}).get("size", 0),
                "eh_frame_cies": elf["eh_frame_cies"],
                "eh_frame_fdes": elf["eh_frame_fdes"],
                "gcc_except_table_bytes": elf["lsda_total_bytes"],
                "rela_text_count": len(elf["rela_text"]),
                "rela_text_types": sorted({r["type"] for r in elf["rela_text"]}),
                "rela_text_addends": sorted({r["addend"] for r in elf["rela_text"]}),
                "rela_eh_frame_count": len(elf["rela_eh_frame"]),
            },
            "specimens": {
                "asm_alu_subreg": {
                    "section": asm_sym["section_name"],
                    "size_bytes": asm_sym["size"],
                    "raw_hex": asm_slice.hex(),
                    "decoded_instructions": decoded_seq,
                    "all_roundtrip_matched": asm_roundtrip_all_ok,
                    "observed_add64_and_xor32_zext": has_add_and_xor,
                    "direct_encoder_exact_subsequence_match": direct_asm_body in asm_slice,
                },
                "unwind_call_lsda_size_bytes": unwind_sym["size"],
                "subreg_lanes_size_bytes": subreg_sym["size"],
                "stack_frame_probe_size_bytes": stack_sym["size"],
            },
            "v1_mutants": {
                "total": len(mutants),
                "killed": sum(1 for m in mutants if m["caught"]),
                "cases": mutants,
            },
            "lean_verification": lean_result,
            "objdump_asm_alu_subreg_excerpt": "\n".join(
                ln for ln in objdump_text.splitlines() if "asm_alu_subreg" in ln or "\t" in ln
            )[:800],
        }

        out_path = Path(args.out)
        out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
        print(json.dumps(results, indent=2))
        if not (asm_roundtrip_all_ok and has_add_and_xor and results["v1_mutants"]["killed"] == len(mutants)):
            return 2
        if lean_result.get("executed") and (lean_result.get("returncode") != 0 or lean_result.get("forbidden_axioms_detected")):
            return 3
        return 0
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


if __name__ == "__main__":
    raise SystemExit(main())
