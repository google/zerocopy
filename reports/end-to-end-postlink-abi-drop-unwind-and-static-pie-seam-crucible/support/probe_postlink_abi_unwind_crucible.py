#!/usr/bin/env python3
"""Live multi-crate rustc + dual-linker (GNU ld vs. rust-lld) seam crucible probe.

Compiles, links, disassembles, parses ELF64/.eh_frame_hdr/.eh_frame/.gcc_except_table,
and executes native specimens across:
  1. 4-way FnAbi PassMode (Direct, Pair niche, Cast 12B C-unwind, Indirect 40B sret)
     x ElaborateDrops (Static, Conditional, partial-move Open) x {normal, cross-crate panic};
  2. Double-panic during cross-crate unwind (Static drop_in_place sibling execution vs.
     Open inline terminate(cleanup) filter_landing_pad immediate abort);
  3. Post-link instruction/relocation verification, LSDA [cs_start, cs_start + cs_len)
     containment under ret_rip - 1 vs. naive ret_rip off-by-one on trailing noreturn calls,
     inter-function padding (0xCC int3 in rust-lld vs. NOP sleds in GNU ld), and >32 KiB
     inline 4096-byte stack-clash probe loop DWARF CFA (%r11 -> %rsp) accuracy;
  4. Multi-crate freestanding #![no_std] -C relocation-model=pie -C link-arg=-static-pie
     startup hazard (GNU ld GOTPCREL mov->lea relaxation vs. rust-lld unrelaxed GOT load SIGSEGV).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import struct
import subprocess
import sys
import tempfile
import time
from pathlib import Path
from typing import Any


DW_EH_PE_omit = 0xFF
DW_EH_PE_absptr = 0x00
DW_EH_PE_uleb128 = 0x01
DW_EH_PE_udata2 = 0x02
DW_EH_PE_udata4 = 0x03
DW_EH_PE_udata8 = 0x04
DW_EH_PE_sleb128 = 0x09
DW_EH_PE_sdata2 = 0x0A
DW_EH_PE_sdata4 = 0x0B
DW_EH_PE_sdata8 = 0x0C
DW_EH_PE_pcrel = 0x10
DW_EH_PE_textrel = 0x20
DW_EH_PE_datarel = 0x30
DW_EH_PE_funcrel = 0x40
DW_EH_PE_indirect = 0x80


def find_tool(name: str) -> str:
    extra_dirs = [
        Path.home() / ".cargo" / "bin",
        Path.home() / ".elan" / "bin",
        Path.home() / ".local" / "bin",
    ]
    path_env = os.pathsep.join(
        [str(d) for d in extra_dirs if d.is_dir()] + [os.environ.get("PATH", "")]
    )
    found = shutil.which(name, path=path_env)
    if not found:
        raise RuntimeError(f"Required tool {name!r} not found in PATH={path_env}")
    return found


def run_cmd(
    argv: list[str],
    *,
    cwd: Path | None = None,
    env: dict[str, str] | None = None,
    check: bool = True,
    timeout: float = 120.0,
) -> subprocess.CompletedProcess[str]:
    merged_env = os.environ.copy()
    merged_env["PATH"] = os.pathsep.join(
        [
            str(Path.home() / ".cargo" / "bin"),
            str(Path.home() / ".local" / "bin"),
            merged_env.get("PATH", ""),
        ]
    )
    if env:
        merged_env.update(env)
    res = subprocess.run(
        argv,
        cwd=str(cwd) if cwd else None,
        env=merged_env,
        text=True,
        capture_output=True,
        timeout=timeout,
    )
    if check and res.returncode != 0:
        raise RuntimeError(
            f"Command failed (rc={res.returncode}): {' '.join(argv)}\n"
            f"STDOUT:\n{res.stdout[-2000:]}\nSTDERR:\n{res.stderr[-2000:]}"
        )
    return res


def read_uleb128(buf: bytes, pos: int) -> tuple[int, int]:
    result = 0
    shift = 0
    while True:
        b = buf[pos]
        pos += 1
        result |= (b & 0x7F) << shift
        if (b & 0x80) == 0:
            return result, pos
        shift += 7


def read_sleb128(buf: bytes, pos: int) -> tuple[int, int]:
    result = 0
    shift = 0
    while True:
        b = buf[pos]
        pos += 1
        result |= (b & 0x7F) << shift
        shift += 7
        if (b & 0x80) == 0:
            if shift < 64 and (b & 0x40) != 0:
                result |= -(1 << shift)
            return result, pos


class Elf64Image:
    """Minimal pure-Python ELF64 section + symbol + DWARF EH/LSDA reader."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.data = path.read_bytes()
        if self.data[:4] != b"\x7fELF" or self.data[4] != 2 or self.data[5] != 1:
            raise ValueError(f"{path}: expected 64-bit little-endian ELF")
        (
            _e_type,
            _e_machine,
            _e_version,
            self.e_entry,
            _e_phoff,
            e_shoff,
            _e_flags,
            _e_ehsize,
            _e_phentsize,
            _e_phnum,
            e_shentsize,
            e_shnum,
            e_shstrndx,
        ) = struct.unpack_from("<HHIQQQIHHHHHH", self.data, 16)

        raw_shdrs = []
        for i in range(e_shnum):
            off = e_shoff + i * e_shentsize
            raw_shdrs.append(struct.unpack_from("<IIQQQQIIQQ", self.data, off))

        shstr_off = raw_shdrs[e_shstrndx][4]
        shstr_size = raw_shdrs[e_shstrndx][5]
        shstr = self.data[shstr_off : shstr_off + shstr_size]

        self.sections: dict[str, dict[str, Any]] = {}
        self.section_list: list[dict[str, Any]] = []
        for idx, sh in enumerate(raw_shdrs):
            name_off, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, sh_align, sh_entsize = sh
            end = shstr.find(b"\x00", name_off)
            name = shstr[name_off:end].decode("utf-8", errors="replace") if end != -1 else ""
            info = {
                "index": idx,
                "name": name,
                "type": sh_type,
                "flags": sh_flags,
                "addr": sh_addr,
                "offset": sh_offset,
                "size": sh_size,
                "link": sh_link,
                "info": sh_info,
                "align": sh_align,
                "entsize": sh_entsize,
            }
            self.section_list.append(info)
            if name and name not in self.sections:
                self.sections[name] = info

        self.symbols: dict[str, dict[str, Any]] = {}
        self._load_symbols()

    def _load_symbols(self) -> None:
        for sec in self.section_list:
            if sec["type"] not in (2, 11):  # SHT_SYMTAB, SHT_DYNSYM
                continue
            str_sec = self.section_list[sec["link"]]
            strtab = self.data[str_sec["offset"] : str_sec["offset"] + str_sec["size"]]
            entsize = sec["entsize"] or 24
            count = sec["size"] // entsize
            for i in range(count):
                off = sec["offset"] + i * entsize
                st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                    "<IBBHQQ", self.data, off
                )
                if st_name == 0:
                    continue
                end = strtab.find(b"\x00", st_name)
                name = strtab[st_name:end].decode("utf-8", errors="replace") if end != -1 else ""
                if name and (name not in self.symbols or st_value != 0):
                    self.symbols[name] = {
                        "value": st_value,
                        "size": st_size,
                        "info": st_info,
                        "other": st_other,
                        "shndx": st_shndx,
                    }

    def va_to_file_offset(self, va: int) -> int | None:
        for sec in self.section_list:
            if sec["type"] == 8:  # SHT_NOBITS
                continue
            if sec["addr"] != 0 and sec["addr"] <= va < sec["addr"] + sec["size"]:
                return sec["offset"] + (va - sec["addr"])
        return None

    def read_at_va(self, va: int, size: int) -> bytes:
        foff = self.va_to_file_offset(va)
        if foff is None:
            raise ValueError(f"VA 0x{va:x} not mapped in non-NOBITS sections")
        return self.data[foff : foff + size]

    def decode_eh_val(self, buf: bytes, pos: int, enc: int) -> tuple[int, int]:
        fmt = enc & 0x0F
        if fmt == DW_EH_PE_absptr:
            return struct.unpack_from("<Q", buf, pos)[0], pos + 8
        if fmt == DW_EH_PE_uleb128:
            return read_uleb128(buf, pos)
        if fmt == DW_EH_PE_udata2:
            return struct.unpack_from("<H", buf, pos)[0], pos + 2
        if fmt == DW_EH_PE_udata4:
            return struct.unpack_from("<I", buf, pos)[0], pos + 4
        if fmt == DW_EH_PE_udata8:
            return struct.unpack_from("<Q", buf, pos)[0], pos + 8
        if fmt == DW_EH_PE_sleb128:
            return read_sleb128(buf, pos)
        if fmt == DW_EH_PE_sdata2:
            return struct.unpack_from("<h", buf, pos)[0], pos + 2
        if fmt == DW_EH_PE_sdata4:
            return struct.unpack_from("<i", buf, pos)[0], pos + 4
        if fmt == DW_EH_PE_sdata8:
            return struct.unpack_from("<q", buf, pos)[0], pos + 8
        raise ValueError(f"Unsupported DWARF EH value encoding 0x{enc:02x}")

    def decode_eh_ptr(
        self,
        buf: bytes,
        pos: int,
        field_va: int,
        enc: int,
        *,
        datarel_base: int = 0,
        funcrel_base: int = 0,
    ) -> tuple[int | None, int]:
        if enc == DW_EH_PE_omit:
            return None, pos
        raw_val, next_pos = self.decode_eh_val(buf, pos, enc)
        if raw_val == 0:
            return None, next_pos
        app = enc & 0x70
        if app == DW_EH_PE_absptr:
            addr = raw_val
        elif app == DW_EH_PE_pcrel:
            addr = (field_va + raw_val) & 0xFFFF_FFFF_FFFF_FFFF
        elif app == DW_EH_PE_datarel:
            addr = (datarel_base + raw_val) & 0xFFFF_FFFF_FFFF_FFFF
        elif app == DW_EH_PE_funcrel:
            addr = (funcrel_base + raw_val) & 0xFFFF_FFFF_FFFF_FFFF
        else:
            raise ValueError(f"Unsupported DWARF EH pointer base 0x{enc:02x}")
        if (enc & DW_EH_PE_indirect) != 0:
            ptr_bytes = self.read_at_va(addr, 8)
            addr = struct.unpack("<Q", ptr_bytes)[0]
        return addr, next_pos

    def parse_eh_frame_hdr(self) -> dict[str, Any]:
        sec = self.sections.get(".eh_frame_hdr")
        if not sec:
            return {"present": False}
        hdr_va = sec["addr"]
        buf = self.data[sec["offset"] : sec["offset"] + sec["size"]]
        version, eh_ptr_enc, fde_cnt_enc, table_enc = struct.unpack_from("<BBBB", buf, 0)
        pos = 4
        eh_frame_ptr, pos = self.decode_eh_ptr(buf, pos, hdr_va + pos, eh_ptr_enc, datarel_base=hdr_va)
        fde_count, pos = self.decode_eh_val(buf, pos, fde_cnt_enc)
        entries = []
        rel_keys = []
        for _ in range(fde_count):
            if table_enc != (DW_EH_PE_datarel | DW_EH_PE_sdata4):
                raise ValueError(f"Unexpected .eh_frame_hdr table_enc=0x{table_enc:02x}")
            init_rel, fde_rel = struct.unpack_from("<ii", buf, pos)
            pos += 8
            rel_keys.append(init_rel)
            entries.append(
                {
                    "init_loc_rel": init_rel,
                    "fde_ptr_rel": fde_rel,
                    "pc_begin": hdr_va + init_rel,
                    "fde_va": hdr_va + fde_rel,
                }
            )
        strictly_sorted = all(rel_keys[i] < rel_keys[i + 1] for i in range(len(rel_keys) - 1))
        neg_keys = sum(1 for k in rel_keys if k < 0)
        pos_keys = sum(1 for k in rel_keys if k > 0)
        eh_sec = self.sections.get(".eh_frame")
        return {
            "present": True,
            "hdr_va": f"0x{hdr_va:x}",
            "header_first_12_hex": buf[:12].hex(" "),
            "version": version,
            "eh_frame_ptr_enc": f"0x{eh_ptr_enc:02x}",
            "fde_count_enc": f"0x{fde_cnt_enc:02x}",
            "table_enc": f"0x{table_enc:02x}",
            "eh_frame_ptr_matches_section": bool(eh_sec and eh_frame_ptr == eh_sec["addr"]),
            "fde_count": fde_count,
            "strictly_sorted": strictly_sorted,
            "negative_init_loc_rel_count": neg_keys,
            "positive_init_loc_rel_count": pos_keys,
            "entries": entries,
        }

    def parse_eh_frame_and_lsda(self) -> tuple[list[dict[str, Any]], dict[int, dict[str, Any]]]:
        sec = self.sections.get(".eh_frame")
        if not sec:
            return [], {}
        base_va = sec["addr"]
        buf = self.data[sec["offset"] : sec["offset"] + sec["size"]]
        cies: dict[int, dict[str, Any]] = {}
        fdes: list[dict[str, Any]] = []
        pos = 0
        while pos + 4 <= len(buf):
            rec_start = pos
            length = struct.unpack_from("<I", buf, pos)[0]
            pos += 4
            if length == 0:
                break
            if length == 0xFFFFFFFF:
                length = struct.unpack_from("<Q", buf, pos)[0]
                pos += 8
            rec_end = pos + length
            id_field_pos = pos
            cie_id = struct.unpack_from("<I", buf, pos)[0]
            pos += 4
            if cie_id == 0:
                ver = buf[pos]
                pos += 1
                aug_end = buf.find(b"\x00", pos)
                aug = buf[pos:aug_end].decode("ascii", errors="replace")
                pos = aug_end + 1
                code_align, pos = read_uleb128(buf, pos)
                data_align, pos = read_sleb128(buf, pos)
                ret_reg, pos = read_uleb128(buf, pos)
                lsda_enc = DW_EH_PE_omit
                fde_enc = DW_EH_PE_absptr
                pers_va = None
                if aug.startswith("z"):
                    aug_len, pos = read_uleb128(buf, pos)
                    aug_end_pos = pos + aug_len
                    for ch in aug[1:]:
                        if ch == "L":
                            lsda_enc = buf[pos]
                            pos += 1
                        elif ch == "P":
                            p_enc = buf[pos]
                            pos += 1
                            pers_va, pos = self.decode_eh_ptr(buf, pos, base_va + pos, p_enc)
                        elif ch == "R":
                            fde_enc = buf[pos]
                            pos += 1
                        elif ch == "S":
                            pass
                    pos = aug_end_pos
                cies[rec_start] = {
                    "offset": rec_start,
                    "va": base_va + rec_start,
                    "version": ver,
                    "augmentation": aug,
                    "code_align": code_align,
                    "data_align": data_align,
                    "ret_reg": ret_reg,
                    "lsda_enc": lsda_enc,
                    "fde_enc": fde_enc,
                    "personality_va": pers_va,
                }
            else:
                cie_off = id_field_pos - cie_id
                cie = cies[cie_off]
                fde_enc = cie["fde_enc"]
                pc_begin, pos = self.decode_eh_ptr(buf, pos, base_va + pos, fde_enc)
                pc_range, pos = self.decode_eh_val(buf, pos, fde_enc & 0x0F)
                lsda_va = None
                if cie["augmentation"].startswith("z"):
                    aug_len, pos = read_uleb128(buf, pos)
                    aug_end_pos = pos + aug_len
                    if "L" in cie["augmentation"] and aug_len > 0 and cie["lsda_enc"] != DW_EH_PE_omit:
                        lsda_va, _ = self.decode_eh_ptr(buf, pos, base_va + pos, cie["lsda_enc"])
                    pos = aug_end_pos
                assert pc_begin is not None
                lsda_info = self.parse_lsda(lsda_va, pc_begin) if lsda_va else None
                fdes.append(
                    {
                        "fde_va": base_va + rec_start,
                        "cie_offset": cie_off,
                        "pc_begin": pc_begin,
                        "pc_end": pc_begin + pc_range,
                        "pc_range": pc_range,
                        "personality_va": cie["personality_va"],
                        "lsda_va": lsda_va,
                        "lsda": lsda_info,
                    }
                )
            pos = rec_end
        return fdes, cies

    def parse_lsda(self, lsda_va: int, func_start: int) -> dict[str, Any]:
        foff = self.va_to_file_offset(lsda_va)
        if foff is None:
            raise ValueError(f"LSDA VA 0x{lsda_va:x} unmapped")
        buf = self.data
        pos = foff
        lpstart_enc = buf[pos]
        pos += 1
        if lpstart_enc != DW_EH_PE_omit:
            lpad_base, pos = self.decode_eh_ptr(
                buf, pos, lsda_va + (pos - foff), lpstart_enc, funcrel_base=func_start
            )
            assert lpad_base is not None
        else:
            lpad_base = func_start

        ttype_enc = buf[pos]
        pos += 1
        if ttype_enc != DW_EH_PE_omit:
            _ttype_off, pos = read_uleb128(buf, pos)

        cs_enc = buf[pos]
        pos += 1
        cs_table_len, pos = read_uleb128(buf, pos)
        cs_table_end = pos + cs_table_len
        action_table_pos = cs_table_end

        call_sites = []
        while pos < cs_table_end:
            cs_start, pos = self.decode_eh_val(buf, pos, cs_enc)
            cs_len, pos = self.decode_eh_val(buf, pos, cs_enc)
            cs_lpad, pos = self.decode_eh_val(buf, pos, cs_enc)
            cs_action, pos = read_uleb128(buf, pos)
            ttype_index = None
            action_kind = "None" if cs_lpad == 0 else "Cleanup"
            if cs_lpad != 0 and cs_action != 0:
                act_pos = action_table_pos + cs_action - 1
                ttype_index, _ = read_sleb128(buf, act_pos)
                if ttype_index == 0:
                    action_kind = "Cleanup"
                elif ttype_index > 0:
                    action_kind = "Catch"
                else:
                    action_kind = "Filter_Terminate"
            call_sites.append(
                {
                    "cs_start": cs_start,
                    "cs_len": cs_len,
                    "cs_lpad": cs_lpad,
                    "cs_action": cs_action,
                    "ttype_index": ttype_index,
                    "action_kind": action_kind,
                    "range_va_start": func_start + cs_start,
                    "range_va_end": func_start + cs_start + cs_len,
                    "lpad_va": (lpad_base + cs_lpad) if cs_lpad != 0 else None,
                }
            )
        return {
            "lsda_va": f"0x{lsda_va:x}",
            "cs_enc": f"0x{cs_enc:02x}",
            "call_sites": call_sites,
        }


def eh_frame_hdr_lookup(hdr_entries: list[dict[str, Any]], fde_by_va: dict[int, dict[str, Any]], query_pc: int) -> dict[str, Any]:
    """Simulate libunwind/libgcc .eh_frame_hdr binary search (upper_bound - 1 on pc_begin) + FDE range check."""
    lo, hi = 0, len(hdr_entries)
    while lo < hi:
        mid = (lo + hi) // 2
        if hdr_entries[mid]["pc_begin"] <= query_pc:
            lo = mid + 1
        else:
            hi = mid
    if lo == 0:
        return {"matched": False, "reason": "below_first_fde"}
    cand = hdr_entries[lo - 1]
    fde = fde_by_va.get(cand["fde_va"])
    if not fde:
        return {"matched": False, "reason": "missing_fde"}
    in_range = fde["pc_begin"] <= query_pc < fde["pc_end"]
    return {
        "matched": in_range,
        "candidate_fde_pc_begin": f"0x{fde['pc_begin']:x}",
        "candidate_fde_pc_end": f"0x{fde['pc_end']:x}",
        "reason": "ok" if in_range else "outside_candidate_fde_range",
        "fde": fde if in_range else None,
    }


def lsda_lookup(lsda: dict[str, Any] | None, query_ip: int) -> dict[str, Any]:
    """Simulate library/std/src/sys/personality/dwarf/eh.rs::find_eh_action."""
    if lsda is None:
        return {"eh_action": "None", "matched_cs": None}
    for cs in lsda["call_sites"]:
        if query_ip < cs["range_va_start"]:
            break
        if query_ip < cs["range_va_end"]:
            if cs["cs_lpad"] == 0:
                return {"eh_action": "None", "matched_cs": cs}
            return {
                "eh_action": cs["action_kind"],
                "lpad_va": f"0x{cs['lpad_va']:x}" if cs["lpad_va"] else None,
                "matched_cs": cs,
            }
    return {"eh_action": "Terminate_Gap", "matched_cs": None}


INSN_LINE_RE = re.compile(r"^\s*([0-9a-fA-F]+):\s+((?:[0-9a-fA-F]{2}\s)+)\s*(.*)$")
FUNC_HDR_RE = re.compile(r"^([0-9a-fA-F]+)\s+<([^>]+)>:$")


def parse_objdump_functions(objdump_text: str) -> dict[str, list[dict[str, Any]]]:
    funcs: dict[str, list[dict[str, Any]]] = {}
    cur_name: str | None = None
    for line in objdump_text.splitlines():
        m_hdr = FUNC_HDR_RE.match(line.strip())
        if m_hdr:
            cur_name = m_hdr.group(2)
            funcs[cur_name] = []
            continue
        if cur_name is None:
            continue
        m_ins = INSN_LINE_RE.match(line)
        if m_ins:
            addr = int(m_ins.group(1), 16)
            raw_bytes = [int(b, 16) for b in m_ins.group(2).strip().split()]
            asm = m_ins.group(3).strip()
            funcs[cur_name].append(
                {
                    "addr": addr,
                    "size": len(raw_bytes),
                    "bytes_hex": " ".join(f"{b:02x}" for b in raw_bytes),
                    "asm": asm,
                }
            )
    return funcs


def parse_reloc_counts(readelf_r_text: str) -> dict[str, int]:
    counts: dict[str, int] = {}
    for line in readelf_r_text.splitlines():
        for m in re.finditer(r"\b(R_X86_64_[A-Z0-9_]+)\b", line):
            k = m.group(1)
            counts[k] = counts.get(k, 0) + 1
    return dict(sorted(counts.items()))


def extract_llvm_signatures(ll_text: str, fn_names: list[str]) -> dict[str, str]:
    sigs: dict[str, str] = {}
    for line in ll_text.splitlines():
        if not line.startswith("define "):
            continue
        for fn in fn_names:
            if f"@{fn}(" in line:
                sigs[fn] = line.strip()
    return sigs


def extract_mir_summary(mir_dir: Path) -> dict[str, Any]:
    summary: dict[str, Any] = {}
    targets = [
        "caller_four_way_seam",
        "caller_double_panic_static",
        "caller_double_panic_open",
        "drop_in_place",
    ]
    for p in sorted(mir_dir.glob("*ElaborateDrops.after.mir")):
        txt = p.read_text(encoding="utf-8", errors="replace")
        fname = p.name
        if not any(t in fname for t in targets):
            continue
        cleanup_bbs = len(re.findall(r"bb\d+\s*\(cleanup\):", txt))
        terminate_cleanup = len(re.findall(r"unwind terminate\(cleanup\)", txt))
        unwind_bb = len(re.findall(r"unwind:\s*bb\d+", txt))
        drop_terms = len(re.findall(r"\bdrop\(", txt))
        switch_ints = len(re.findall(r"\bswitchInt\(", txt))
        summary[fname] = {
            "cleanup_basic_blocks": cleanup_bbs,
            "drop_terminators": drop_terms,
            "unwind_to_cleanup_edges": unwind_bb,
            "unwind_terminate_cleanup_edges": terminate_cleanup,
            "switch_int_terminators": switch_ints,
        }
    return summary


def extract_stack_clash_cfi(frames_interp_text: str, fde_start: int, fde_end: int) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    row_re = re.compile(r"^\s*([0-9a-fA-F]{8,16})\s+(\S+)\s+(.*)$")
    for line in frames_interp_text.splitlines():
        m = row_re.match(line)
        if not m:
            continue
        loc = int(m.group(1), 16)
        if fde_start <= loc <= fde_end:
            rows.append({"loc": f"0x{loc:x}", "cfa": m.group(2), "rest": m.group(3).strip()})
    return rows


def probe_std_config(
    rustc: str,
    objdump: str,
    readelf: str,
    specimens_dir: Path,
    work_dir: Path,
    cfg_name: str,
    opt_level: str,
    linker_args: list[str],
    relax_elf: bool,
) -> dict[str, Any]:
    cdir = work_dir / cfg_name
    cdir.mkdir(parents=True, exist_ok=True)
    mir_dir = cdir / "mir"
    mir_dir.mkdir(exist_ok=True)

    common_flags = ["-C", f"opt-level={opt_level}", "-C", "panic=unwind"]
    if relax_elf:
        common_flags += ["-Z", "relax-elf-relocations=yes"]

    t0 = time.monotonic()
    # 1. Build crate_callee (.rlib + .ll + .o)
    run_cmd(
        [
            rustc,
            "--edition=2021",
            *common_flags,
            "--emit=link,llvm-ir,obj",
            str(specimens_dir / "crate_callee.rs"),
            "--out-dir",
            str(cdir),
        ]
    )
    rlib_path = cdir / "libcrate_callee.rlib"
    callee_obj = cdir / "crate_callee.o"

    # 2. Build crate_caller (bin + .ll + .o + ElaborateDrops MIR)
    caller_bin = cdir / "crate_caller_bin"
    run_cmd(
        [
            rustc,
            "--edition=2021",
            *common_flags,
            *linker_args,
            f"-Zdump-mir=ElaborateDrops",
            f"-Zdump-mir-dir={mir_dir}",
            "--extern",
            f"crate_callee={rlib_path}",
            "--emit=link,llvm-ir,obj",
            str(specimens_dir / "crate_caller.rs"),
            "-o",
            str(caller_bin),
        ]
    )
    caller_obj = cdir / (caller_bin.name + ".o")
    if not caller_obj.exists():
        cand = list(cdir.glob("crate_caller*.o"))
        caller_obj = cand[0]
    compile_link_sec = round(time.monotonic() - t0, 4)

    # 3. Run single-process test matrix
    run_res = run_cmd([str(caller_bin)])
    scenario_rows = {}
    for line in run_res.stdout.strip().splitlines():
        parts = line.split("|", 2)
        if len(parts) == 3:
            scenario_rows[parts[0]] = {
                "outcome": parts[1],
                "events": parts[2].split(",") if parts[2] else [],
            }

    # 4. Run double-panic subprocesses (Static vs Open)
    dp_results = {}
    for dp_mode in ("double_panic_static", "double_panic_open"):
        dp_proc = run_cmd(
            [str(caller_bin), dp_mode],
            env={"CRUCIBLE_STDERR_TRACE": "1", "RUST_BACKTRACE": "0"},
            check=False,
        )
        trace_drops = [
            ln.split("TRACE_DROP:", 1)[1].strip()
            for ln in dp_proc.stderr.splitlines()
            if "TRACE_DROP:" in ln
        ]
        dp_results[dp_mode] = {
            "returncode": dp_proc.returncode,
            "trace_drops_before_abort": trace_drops,
            "panicked_in_cleanup_msg": (
                "panicked while processing panic" in dp_proc.stderr
                or "panic in a destructor during cleanup" in dp_proc.stderr
            ),
            "stderr_tail": dp_proc.stderr.splitlines()[-6:],
        }

    # 5. LLVM IR signatures & MIR drop summary
    callee_ll = (cdir / "crate_callee.ll").read_text(encoding="utf-8", errors="replace")
    llvm_sigs = extract_llvm_signatures(
        callee_ll,
        [
            "callee_direct",
            "callee_pair_niche",
            "callee_cast_12",
            "callee_indirect_sret",
            "callee_noreturn_panic",
        ],
    )
    mir_summary = extract_mir_summary(mir_dir)

    # 6. Pre-link & post-link relocations and disassembly
    pre_caller_relocs = parse_reloc_counts(run_cmd([readelf, "-rW", str(caller_obj)]).stdout)
    pre_callee_relocs = parse_reloc_counts(run_cmd([readelf, "-rW", str(callee_obj)]).stdout)
    post_relocs = parse_reloc_counts(run_cmd([readelf, "-rW", str(caller_bin)]).stdout)

    pre_caller_dis = parse_objdump_functions(run_cmd([objdump, "-dr", str(caller_obj)]).stdout)
    post_dis_text = run_cmd([objdump, "-d", str(caller_bin)]).stdout
    post_dis = parse_objdump_functions(post_dis_text)

    # Count total int3 vs nop across .text
    int3_count = sum(
        1 for insns in post_dis.values() for i in insns if i["asm"].startswith("int3")
    )
    nop_count = sum(
        1 for insns in post_dis.values() for i in insns if i["asm"].startswith(("nop", "data16 cs nop", "cs nop"))
    )

    # 7. Parse ELF64 .eh_frame_hdr + .eh_frame + .gcc_except_table LSDA
    elf = Elf64Image(caller_bin)
    eh_hdr = elf.parse_eh_frame_hdr()
    fdes, _cies = elf.parse_eh_frame_and_lsda()
    fde_by_va = {f["fde_va"]: f for f in fdes}
    fde_by_pc = {f["pc_begin"]: f for f in fdes}
    sorted_fdes = sorted(fdes, key=lambda x: x["pc_begin"])

    # Verify .eh_frame_hdr matches every FDE pc_begin
    hdr_pc_mismatches = 0
    for ent in eh_hdr.get("entries", []):
        f = fde_by_va.get(ent["fde_va"])
        if not f or f["pc_begin"] != ent["pc_begin"]:
            hdr_pc_mismatches += 1

    # 8. Inspect target probe functions for call-site LSDA containment, GOT relaxation, noreturn boundary, & stack-clash CFI
    target_fns = [
        "caller_four_way_seam",
        "caller_trailing_noreturn_with_cleanup",
        "caller_bare_trailing_noreturn",
        "caller_aligned_trailing_noreturn",
        "caller_stack_clash_loop_unwind",
        "caller_double_panic_static",
        "caller_double_panic_open",
        "callee_direct",
        "callee_pair_niche",
        "callee_cast_12",
        "callee_indirect_sret",
        "callee_noreturn_panic",
    ]

    fn_audits: dict[str, Any] = {}
    total_call_sites_checked = 0
    ret_minus_1_fde_passes = 0
    naive_ret_fde_failures = 0
    naive_ret_lsda_mismatches = 0

    for fn in target_fns:
        sym = elf.symbols.get(fn)
        if not sym:
            continue
        fn_va = sym["value"]
        fn_size = sym["size"]
        fde = fde_by_pc.get(fn_va)
        insns = post_dis.get(fn, [])
        # Trim trailing alignment padding outside fn_size
        real_insns = [ins for ins in insns if ins["addr"] < fn_va + fn_size]
        padding_insns = [ins for ins in insns if ins["addr"] >= fn_va + fn_size]

        # Also read raw 8 bytes right at fn_va + fn_size in .text to see exact inter-function bytes
        after_end_bytes_hex = ""
        next_fde_pc = None
        if fde:
            idx_in_sorted = next(
                (i for i, x in enumerate(sorted_fdes) if x["pc_begin"] == fde["pc_begin"]),
                None,
            )
            if idx_in_sorted is not None and idx_in_sorted + 1 < len(sorted_fdes):
                next_fde_pc = sorted_fdes[idx_in_sorted + 1]["pc_begin"]
            try:
                after_end_bytes_hex = elf.read_at_va(fde["pc_end"], 8).hex(" ")
            except ValueError:
                after_end_bytes_hex = ""

        call_records = []
        for ins in real_insns:
            mnem = ins["asm"].split()[0] if ins["asm"] else ""
            if not mnem.startswith("call"):
                continue
            total_call_sites_checked += 1
            call_va = ins["addr"]
            ret_rip = call_va + ins["size"]
            q_sub1 = ret_rip - 1

            hdr_sub1 = eh_frame_hdr_lookup(eh_hdr["entries"], fde_by_va, q_sub1)
            hdr_naive = eh_frame_hdr_lookup(eh_hdr["entries"], fde_by_va, ret_rip)

            if hdr_sub1["matched"] and hdr_sub1["fde"]["pc_begin"] == fn_va:
                ret_minus_1_fde_passes += 1
            if not hdr_naive["matched"] or hdr_naive["fde"]["pc_begin"] != fn_va:
                naive_ret_fde_failures += 1

            lsda_sub1 = lsda_lookup(fde["lsda"] if fde else None, q_sub1)
            lsda_naive = lsda_lookup(fde["lsda"] if fde else None, ret_rip)
            if (
                lsda_sub1["eh_action"] != lsda_naive["eh_action"]
                or lsda_sub1.get("lpad_va") != lsda_naive.get("lpad_va")
            ):
                naive_ret_lsda_mismatches += 1

            call_records.append(
                {
                    "call_va": f"0x{call_va:x}",
                    "rel_off": f"0x{call_va - fn_va:x}",
                    "size": ins["size"],
                    "bytes_hex": ins["bytes_hex"],
                    "asm": ins["asm"],
                    "ret_rip": f"0x{ret_rip:x}",
                    "at_fde_end": bool(fde and ret_rip == fde["pc_end"]),
                    "fde_lookup_ret_minus_1": {
                        "matched_caller_fde": bool(
                            hdr_sub1["matched"] and hdr_sub1["fde"]["pc_begin"] == fn_va
                        ),
                        "reason": hdr_sub1["reason"],
                    },
                    "fde_lookup_naive_ret": {
                        "matched_caller_fde": bool(
                            hdr_naive["matched"] and hdr_naive["fde"]["pc_begin"] == fn_va
                        ),
                        "candidate_fde_pc_begin": hdr_naive.get("candidate_fde_pc_begin"),
                        "reason": hdr_naive["reason"],
                    },
                    "lsda_ret_minus_1": {
                        "eh_action": lsda_sub1["eh_action"],
                        "lpad_va": lsda_sub1.get("lpad_va"),
                    },
                    "lsda_naive_ret": {
                        "eh_action": lsda_naive["eh_action"],
                        "lpad_va": lsda_naive.get("lpad_va"),
                    },
                }
            )

        # Record GOT-related mov vs lea in caller_four_way_seam and callee_direct
        got_data_insns = [
            {
                "rel_off": f"0x{ins['addr'] - fn_va:x}",
                "bytes_hex": ins["bytes_hex"],
                "asm": ins["asm"],
            }
            for ins in real_insns
            if "CALLEE_GLOBAL_BIAS" in ins["asm"] or "%rip)" in ins["asm"]
        ]

        fn_audits[fn] = {
            "fn_va": f"0x{fn_va:x}",
            "fn_size": fn_size,
            "fde_pc_begin": f"0x{fde['pc_begin']:x}" if fde else None,
            "fde_pc_end": f"0x{fde['pc_end']:x}" if fde else None,
            "fde_pc_range": fde["pc_range"] if fde else None,
            "next_fde_pc_begin": f"0x{next_fde_pc:x}" if next_fde_pc else None,
            "gap_to_next_fde_bytes": (next_fde_pc - fde["pc_end"]) if (fde and next_fde_pc) else None,
            "bytes_at_fde_end_hex": after_end_bytes_hex,
            "padding_insns": padding_insns[:6],
            "lsda_call_site_count": len(fde["lsda"]["call_sites"]) if (fde and fde["lsda"]) else 0,
            "lsda_call_sites": (
                [
                    {
                        "cs_start": f"0x{cs['cs_start']:x}",
                        "cs_len": f"0x{cs['cs_len']:x}",
                        "cs_lpad": f"0x{cs['cs_lpad']:x}",
                        "action_kind": cs["action_kind"],
                        "ttype_index": cs["ttype_index"],
                    }
                    for cs in fde["lsda"]["call_sites"]
                ]
                if (fde and fde["lsda"])
                else []
            ),
            "calls": call_records,
            "rip_rel_insns_sample": got_data_insns[:8],
            "pre_link_insns_sample": pre_caller_dis.get(fn, [])[:10],
        }

    # Scan ALL FDEs in the binary to count how many end with a `call` where `ret_rip == fde_end`
    # and how many of those have `gap_to_next_fde == 0` (`ret_rip == next_fde.pc_begin`)!
    binary_wide_trailing_calls = 0
    binary_wide_zero_gap_trailing_calls = 0
    trailing_call_examples = []
    addr_to_ins = {
        ins["addr"]: (fn_name, ins)
        for fn_name, insns in post_dis.items()
        for ins in insns
    }
    for idx, f in enumerate(sorted_fdes):
        # Check whether an instruction ending at f["pc_end"] is a 5B or 6B call
        for cand_len in (5, 6):
            pair = addr_to_ins.get(f["pc_end"] - cand_len)
            if not pair:
                continue
            fn_name, ins = pair
            if ins["size"] == cand_len and ins["asm"].startswith("call"):
                binary_wide_trailing_calls += 1
                nxt_pc = sorted_fdes[idx + 1]["pc_begin"] if idx + 1 < len(sorted_fdes) else None
                gap = (nxt_pc - f["pc_end"]) if nxt_pc is not None else None
                if gap == 0:
                    binary_wide_zero_gap_trailing_calls += 1
                if len(trailing_call_examples) < 8:
                    trailing_call_examples.append(
                        {
                            "function": fn_name,
                            "fde_pc_begin": f"0x{f['pc_begin']:x}",
                            "fde_pc_end": f"0x{f['pc_end']:x}",
                            "call_va": f"0x{ins['addr']:x}",
                            "call_bytes": ins["bytes_hex"],
                            "call_asm": ins["asm"],
                            "next_fde_pc_begin": f"0x{nxt_pc:x}" if nxt_pc else None,
                            "gap_to_next_fde_bytes": gap,
                        }
                    )

    # 9. Extract interpreted DWARF CFI rows for caller_stack_clash_loop_unwind
    frames_interp = run_cmd([readelf, "--debug-dump=frames-interp", str(caller_bin)]).stdout
    sc_sym = elf.symbols.get("caller_stack_clash_loop_unwind")
    sc_cfi_rows = []
    sc_prologue_insns = []
    if sc_sym:
        sc_fde = fde_by_pc.get(sc_sym["value"])
        if sc_fde:
            sc_cfi_rows = extract_stack_clash_cfi(
                frames_interp, sc_fde["pc_begin"], sc_fde["pc_end"]
            )
        sc_prologue_insns = post_dis.get("caller_stack_clash_loop_unwind", [])[:18]

    return {
        "config": cfg_name,
        "opt_level": opt_level,
        "linker_args": linker_args,
        "relax_elf_relocations": relax_elf,
        "compile_and_link_sec": compile_link_sec,
        "binary_size_bytes": caller_bin.stat().st_size,
        "section_vas": {
            k: {"addr": f"0x{v['addr']:x}", "size": v["size"]}
            for k, v in elf.sections.items()
            if k in (".rodata", ".eh_frame_hdr", ".eh_frame", ".gcc_except_table", ".text", ".got", ".rela.dyn")
        },
        "pre_link_caller_relocs": pre_caller_relocs,
        "pre_link_callee_relocs": pre_callee_relocs,
        "post_link_dyn_relocs": post_relocs,
        "text_padding_counts": {"int3": int3_count, "nop": nop_count},
        "eh_frame_hdr": {k: v for k, v in eh_hdr.items() if k != "entries"},
        "eh_frame_hdr_pc_mismatches": hdr_pc_mismatches,
        "total_fde_count": len(fdes),
        "probe_call_containment_summary": {
            "total_calls_in_probe_fns": total_call_sites_checked,
            "ret_minus_1_matches_caller_fde": ret_minus_1_fde_passes,
            "naive_ret_fails_caller_fde": naive_ret_fde_failures,
            "naive_ret_lsda_action_or_lpad_mismatches": naive_ret_lsda_mismatches,
            "binary_wide_fde_ending_at_call_count": binary_wide_trailing_calls,
            "binary_wide_zero_gap_fde_ending_at_call_count": binary_wide_zero_gap_trailing_calls,
            "binary_wide_trailing_call_examples": trailing_call_examples,
        },
        "llvm_callee_signatures": llvm_sigs,
        "mir_elaborate_drops_summary": mir_summary,
        "scenarios": scenario_rows,
        "double_panic": dp_results,
        "stack_clash_40k_cfi": {
            "cfi_rows": sc_cfi_rows,
            "prologue_disassembly": sc_prologue_insns,
        },
        "function_audits": fn_audits,
    }


def probe_nostd_static_pie_matrix(
    rustc: str,
    objdump: str,
    readelf: str,
    specimens_dir: Path,
    work_dir: Path,
) -> dict[str, Any]:
    results: dict[str, Any] = {}
    gnu_ld_args = ["-Clinker-flavor=gnu-cc", "-Zunstable-options", "-Clink-self-contained=-linker"]
    lld_args = ["-Clinker-flavor=gnu-lld-cc", "-Zunstable-options"]
    matrix = [
        ("nostd_inline_data_gnu_ld_default", True, False, gnu_ld_args),
        ("nostd_inline_data_rust_lld_default", True, False, lld_args),
        ("nostd_crosscrate_call_gnu_ld_default", False, False, gnu_ld_args),
        ("nostd_crosscrate_call_rust_lld_default", False, False, lld_args),
        ("nostd_crosscrate_call_gnu_ld_relax_yes", False, True, gnu_ld_args),
        ("nostd_crosscrate_call_rust_lld_relax_yes", False, True, lld_args),
    ]
    for name, inline_data, relax_yes, l_args in matrix:
        ndir = work_dir / name
        ndir.mkdir(parents=True, exist_ok=True)
        flags = [
            "--edition=2021",
            "-C",
            "opt-level=2",
            "-C",
            "panic=abort",
            "-C",
            "relocation-model=pie",
        ]
        if relax_yes:
            flags += ["-Z", "relax-elf-relocations=yes"]
        caller_cfg = ["--cfg", "nostd_inline_data"] if inline_data else []

        run_cmd(
            [
                rustc,
                *flags,
                "--emit=link,obj",
                str(specimens_dir / "nostd_callee.rs"),
                "--out-dir",
                str(ndir),
            ]
        )
        rlib = ndir / "libnostd_callee.rlib"
        callee_o = ndir / "nostd_callee.o"
        bin_out = ndir / "nostd_static_pie_bin"
        run_cmd(
            [
                rustc,
                *flags,
                *caller_cfg,
                *l_args,
                "--check-cfg=cfg(nostd_inline_data)",
                "-C",
                "link-arg=-nostdlib",
                "-C",
                "link-arg=-static-pie",
                "--extern",
                f"nostd_callee={rlib}",
                "--emit=link,obj",
                str(specimens_dir / "nostd_caller.rs"),
                "-o",
                str(bin_out),
            ]
        )
        caller_o_cands = list(ndir.glob("nostd_static_pie_bin*.o")) + list(ndir.glob("nostd_caller*.o"))
        caller_o = caller_o_cands[0]
        pre_caller_relocs = parse_reloc_counts(run_cmd([readelf, "-rW", str(caller_o)]).stdout)
        pre_callee_relocs = parse_reloc_counts(run_cmd([readelf, "-rW", str(callee_o)]).stdout)
        post_relocs = parse_reloc_counts(run_cmd([readelf, "-rW", str(bin_out)]).stdout)
        dis_post = parse_objdump_functions(run_cmd([objdump, "-d", str(bin_out)]).stdout)
        dis_pre_caller = parse_objdump_functions(run_cmd([objdump, "-dr", str(caller_o)]).stdout)

        exec_res = run_cmd([str(bin_out)], check=False, timeout=10.0)
        elf = Elf64Image(bin_out)
        got_sec = elf.sections.get(".got")
        got_words_hex = ""
        if got_sec and got_sec["size"] >= 8:
            got_words_hex = elf.data[got_sec["offset"] : got_sec["offset"] + min(got_sec["size"], 32)].hex(" ")

        results[name] = {
            "inline_data_only": inline_data,
            "relax_elf_relocations": relax_yes,
            "linker_args": l_args,
            "pre_link_caller_relocs": pre_caller_relocs,
            "pre_link_callee_relocs": pre_callee_relocs,
            "post_link_dyn_relocs": post_relocs,
            "pre_link_start": dis_pre_caller.get("_start", []),
            "post_link_start": dis_post.get("_start", []),
            "post_link_nostd_sum_calibration": dis_post.get("nostd_sum_calibration", []),
            "got_section_va": f"0x{got_sec['addr']:x}" if got_sec else None,
            "got_first_bytes_hex": got_words_hex,
            "calibration_symbol_va": (
                f"0x{elf.symbols['NOSTD_CALIBRATION_WORDS']['value']:x}"
                if "NOSTD_CALIBRATION_WORDS" in elf.symbols
                else None
            ),
            "exec_returncode": exec_res.returncode,
            "exec_status": "EXIT_OK" if exec_res.returncode == 0 else f"SIGNAL_{exec_res.returncode}",
        }
    return results


def verify_cross_config_invariants(std_configs: dict[str, Any], nostd_configs: dict[str, Any]) -> dict[str, Any]:
    ref_scenarios = std_configs["gnu_ld_default"]["scenarios"]
    all_scenarios_match = all(
        cfg["scenarios"] == ref_scenarios for cfg in std_configs.values()
    )

    # Verify sret panic never drops uninitialized sret_ret_token while normal return drops it once
    sret_ok_events = ref_scenarios["indirect_sret_cm0_pan0"]["events"]
    sret_pan_events = ref_scenarios["indirect_sret_cm0_pan1"]["events"]
    sret_contract_ok = (
        "drop:sret_ret_token" in sret_ok_events
        and "drop:sret_ret_token" not in sret_pan_events
        and "drop:callee_sret_guard" in sret_pan_events
    )

    # Verify Open partial-move drop order (.1 consumed before call; .0 then .2 dropped on unwind, never .1 twice)
    open_pan_events = ref_scenarios["direct_cm0_pan1"]["events"]
    open_order_ok = (
        open_pan_events.count("drop:open_1") == 1
        and open_pan_events.count("drop:open_0") == 1
        and open_pan_events.count("drop:open_2") == 1
        and open_pan_events.index("drop:open_1")
        < open_pan_events.index("drop:open_0")
        < open_pan_events.index("drop:open_2")
    )

    # Verify Conditional drop local: dropped on unwind when cm=0, NOT dropped again when cm=1
    cond_cm0 = ref_scenarios["pair_niche_cm0_pan1"]["events"]
    cond_cm1 = ref_scenarios["pair_niche_cm1_pan1"]["events"]
    cond_flag_ok = (
        cond_cm0.count("drop:cond_0") == 1
        and cond_cm1.count("drop:cond_0") == 1
        and cond_cm1.index("drop:cond_0") < cond_cm1.index("panic:callee_pair")
    )

    # Verify Double-Panic divergence: Static runs f1 & f2 siblings before SIGABRT; Open aborts at f0 before f1!
    dp_divergence_ok = True
    for cfg in std_configs.values():
        st_drops = cfg["double_panic"]["double_panic_static"]["trace_drops_before_abort"]
        op_drops = cfg["double_panic"]["double_panic_open"]["trace_drops_before_abort"]
        if st_drops != [
            "callee_direct_guard",
            "dp_static_f0_bomb",
            "dp_static_f1_sibling",
            "dp_static_f2_sibling",
        ]:
            dp_divergence_ok = False
        if op_drops != [
            "dp_open_f2_moved",
            "callee_direct_guard",
            "dp_open_f0_bomb",
        ]:
            dp_divergence_ok = False

    # Verify #![no_std] -static-pie 6-way startup matrix:
    # - inline cross-crate data load: GNU ld relaxes GOTPCREL mov->lea (0), rust-lld leaves mov unrelaxed (-11)
    # - non-inlined cross-crate call + data load: default GOTPCREL leaves call *got (ff 15) unrelaxed on BOTH (-11, -11),
    #   whereas -Z relax-elf-relocations=yes emits GOTPCRELX + REX_GOTPCRELX and relaxes BOTH to 67 e8 + 48 8d (0, 0)!
    nostd_matrix_ok = (
        nostd_configs["nostd_inline_data_gnu_ld_default"]["exec_returncode"] == 0
        and nostd_configs["nostd_inline_data_rust_lld_default"]["exec_returncode"] == -11
        and nostd_configs["nostd_crosscrate_call_gnu_ld_default"]["exec_returncode"] == -11
        and nostd_configs["nostd_crosscrate_call_rust_lld_default"]["exec_returncode"] == -11
        and nostd_configs["nostd_crosscrate_call_gnu_ld_relax_yes"]["exec_returncode"] == 0
        and nostd_configs["nostd_crosscrate_call_rust_lld_relax_yes"]["exec_returncode"] == 0
    )

    return {
        "all_4_std_configs_identical_scenarios": all_scenarios_match,
        "scenario_count_per_config": len(ref_scenarios),
        "sret_uninit_not_dropped_on_unwind": sret_contract_ok,
        "open_partial_move_declaration_order_verified": open_order_ok,
        "conditional_drop_flag_verified": cond_flag_ok,
        "double_panic_static_vs_open_divergence_verified": dp_divergence_ok,
        "nostd_static_pie_segfault_matrix_verified": nostd_matrix_ok,
    }


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=Path(__file__).resolve().parent / "postlink_abi_unwind_crucible_results.json",
        help="Output JSON path",
    )
    args = parser.parse_args()

    rustc = find_tool("rustc")
    objdump = find_tool("objdump")
    readelf = find_tool("readelf")
    gnu_ld = find_tool("ld")
    specimens_dir = Path(__file__).resolve().parent / "specimens"

    rustc_vv = run_cmd([rustc, "-vV"]).stdout.strip()
    gnu_ld_ver = run_cmd([gnu_ld, "--version"]).stdout.splitlines()[0].strip()
    sysroot = Path(run_cmd([rustc, "--print", "sysroot"]).stdout.strip())
    rust_lld_candidates = list(sysroot.rglob("rust-lld"))
    rust_lld_ver = (
        run_cmd([str(rust_lld_candidates[0]), "-flavor", "gnu", "--version"]).stdout.strip()
        if rust_lld_candidates
        else "unknown"
    )

    with tempfile.TemporaryDirectory(prefix="crucible5_probe_") as tmp:
        work_dir = Path(tmp)
        std_matrix = [
            (
                "gnu_ld_default",
                "0",
                ["-Clinker-flavor=gnu-cc", "-Zunstable-options", "-Clink-self-contained=-linker"],
                False,
            ),
            ("rust_lld_default", "0", ["-Clinker-flavor=gnu-lld-cc", "-Zunstable-options"], False),
            (
                "gnu_ld_relax_o2",
                "2",
                ["-Clinker-flavor=gnu-cc", "-Zunstable-options", "-Clink-self-contained=-linker"],
                True,
            ),
            ("rust_lld_relax_o2", "2", ["-Clinker-flavor=gnu-lld-cc", "-Zunstable-options"], True),
        ]
        std_results = {}
        for cfg_name, opt, l_args, relax in std_matrix:
            std_results[cfg_name] = probe_std_config(
                rustc, objdump, readelf, specimens_dir, work_dir, cfg_name, opt, l_args, relax
            )

        nostd_results = probe_nostd_static_pie_matrix(
            rustc, objdump, readelf, specimens_dir, work_dir
        )

    invariants = verify_cross_config_invariants(std_results, nostd_results)
    specimen_hashes = {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in sorted(specimens_dir.glob("*.rs"))
    }

    payload = {
        "probe": "postlink_abi_drop_unwind_and_static_pie_seam_crucible",
        "observed_date": "2026-11-21",
        "toolchains": {
            "rustc_vV": rustc_vv,
            "gnu_ld_version": gnu_ld_ver,
            "rust_lld_version": rust_lld_ver,
        },
        "specimen_sha256": specimen_hashes,
        "invariants_verified": invariants,
        "std_configs": std_results,
        "nostd_static_pie_configs": nostd_results,
    }

    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(invariants, indent=2))
    if not all(v is True or isinstance(v, int) for v in invariants.values()):
        print("ERROR: One or more crucible invariants failed!", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
