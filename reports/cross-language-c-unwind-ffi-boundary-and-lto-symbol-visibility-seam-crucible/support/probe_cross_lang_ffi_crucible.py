#!/usr/bin/env python3
"""Cross-language Rust <-> C++17 / C17 unwinding, SysV i128 ABI, and ThinLTO/visibility crucible.

Compiles, disassembles, inspects LLVM IR / MIR / ELF64 DWARF EH tables / .dynsym / .symtab,
and executes multi-language binaries across:
  1. All 6 cross-language unwinding cells (+ ThinLTO) across `panic=unwind`, `panic=abort`,
     and `panic=abort -C force-unwind-tables=no`, capturing pre-SIGABRT POSIX `write(2)`
     destructor traces:
       - Cell 1: C++ throw -> Rust `extern "C-unwind"` (`Drop` runs!) -> C++ catch
       - Cell 2: Rust panic! -> C++ RAII (`~CppGuard()` runs!) -> Rust `catch_unwind`
       - Cell 3: Rust `catch_unwind` around C++ throw -> cleanup + `__rust_foreign_exception` abort
       - Cell 4: `-C panic=abort` Rust `extern "C-unwind"` receiving C++ throw -> `Terminate(Reason::Abi)`
       - Cell 5: C++ throw across non-unwind `extern "C"` with uwtable -> silent `Drop` skip UB
       - Cell 6: `-C force-unwind-tables=no` on `extern "C"` -> missing FDE -> `std::terminate`
  2. SysV x86-64 `i128`/`u128` <-> `__int128` ABI parity (`rustc` vs. `clang` C++17 vs. `gcc` C17),
     including 16-byte alignment (`Pair48`, `Mixed64`), register pairs, and the 5-GPR straddle
     stack spill boundary preserving `%r9`.
  3. Cross-language ThinLTO (`rustc -Clinker-plugin-lto` + `clang -flto=thin` via `rust-lld`),
     `STV_DEFAULT` vs. `STV_HIDDEN` symbol visibility in `.rlib`, `cdylib`, and executables,
     `--version-script` localization, and `-C default-linker-libraries`.
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


def find_tools() -> dict[str, str]:
    home = Path.home()
    extra_dirs = [
        home / ".cargo" / "bin",
        home / ".elan" / "bin",
        home / ".local" / "bin",
    ]
    # Also include active rustup toolchain bin dir for llvm-objdump / llvm-ar
    toolchains_dir = home / ".rustup" / "toolchains"
    if toolchains_dir.is_dir():
        for tc in sorted(toolchains_dir.iterdir()):
            tbin = tc / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
            if tbin.is_dir():
                extra_dirs.append(tbin)
    elan_toolchains = home / ".elan" / "toolchains"
    if elan_toolchains.is_dir():
        for tc in sorted(elan_toolchains.iterdir()):
            eb = tc / "bin"
            if eb.is_dir():
                extra_dirs.append(eb)

    search_path = os.pathsep.join(
        [str(d) for d in extra_dirs if d.is_dir()] + [os.environ.get("PATH", "")]
    )

    def req(candidates: list[str]) -> str:
        for cand in candidates:
            found = shutil.which(cand, path=search_path)
            if found:
                return found
        raise RuntimeError(f"Required tool {candidates!r} not found in PATH={search_path}")

    cxx_compiler = req(["clang++", "clang", "g++"])
    cxx_driver_mode = "clang_x_cpp" if Path(cxx_compiler).name == "clang" else "direct_cxx"

    libstdcpp = ""
    for cand in [
        "/usr/lib/x86_64-linux-gnu/libstdc++.so.6",
        "/usr/lib64/libstdc++.so.6",
    ]:
        if Path(cand).exists():
            libstdcpp = cand
            break
    if not libstdcpp and cxx_driver_mode == "clang_x_cpp":
        raise RuntimeError("libstdc++.so.6 not found for C++ exception runtime")

    return {
        "rustc": req(["rustc"]),
        "gcc": req(["gcc"]),
        "cxx": cxx_compiler,
        "cxx_driver_mode": cxx_driver_mode,
        "libstdcpp": libstdcpp,
        "readelf": req(["readelf"]),
        "objdump": req(["llvm-objdump", "objdump"]),
        "ar": req(["llvm-ar", "ar"]),
    }


def run_cmd(
    argv: list[str],
    *,
    cwd: Path | None = None,
    check: bool = True,
    timeout: float = 120.0,
) -> subprocess.CompletedProcess[str]:
    res = subprocess.run(
        argv,
        cwd=str(cwd) if cwd else None,
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


def scrub_text(text: str, workdir: Path, specimens_dir: Path | None = None) -> str:
    """Scrub ephemeral build directory paths, home paths, and PIDs for reproducible artifacts."""
    out = text
    out = out.replace(str(workdir), "<WORKDIR>")
    if specimens_dir is not None:
        out = out.replace(str(specimens_dir), "<SPECIMENS>")
        out = out.replace(str(specimens_dir.parent.parent), "<PKG_DIR>")
    home = str(Path.home())
    if home:
        out = out.replace(home, "<HOME>")
    out = re.sub(r"/tmp/[^\s:\"\']+", "<TMP_PATH>", out)
    out = re.sub(r"thread '([^']+)' \(\d+\) panicked at", r"thread '\1' (<TID>) panicked at", out)
    out = re.sub(r"/rustc/[0-9a-f]{40}/", "<RUSTC_SRC>/", out)
    return out


def parse_trace_events(stderr_text: str) -> tuple[list[str], str]:
    events: list[str] = []
    other_lines: list[str] = []
    for line in stderr_text.splitlines():
        if line.startswith("[TRACE] "):
            events.append(line[len("[TRACE] ") :].strip())
        else:
            other_lines.append(line)
    return events, "\n".join(other_lines)


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


def decode_eh_ptr(
    buf: bytes,
    pos: int,
    enc: int,
    sec_va: int,
    pcrel_base_va: int | None = None,
    datarel_base_va: int = 0,
    funcrel_base_va: int = 0,
) -> tuple[int | None, int]:
    if enc == DW_EH_PE_omit:
        return None, pos
    fmt = enc & 0x0F
    app = enc & 0x70
    field_va = sec_va + pos
    if fmt in (DW_EH_PE_absptr, DW_EH_PE_udata8):
        raw = struct.unpack_from("<Q", buf, pos)[0]
        pos += 8
    elif fmt == DW_EH_PE_sdata8:
        raw = struct.unpack_from("<q", buf, pos)[0]
        pos += 8
    elif fmt == DW_EH_PE_udata4:
        raw = struct.unpack_from("<I", buf, pos)[0]
        pos += 4
    elif fmt == DW_EH_PE_sdata4:
        raw = struct.unpack_from("<i", buf, pos)[0]
        pos += 4
    elif fmt == DW_EH_PE_udata2:
        raw = struct.unpack_from("<H", buf, pos)[0]
        pos += 2
    elif fmt == DW_EH_PE_sdata2:
        raw = struct.unpack_from("<h", buf, pos)[0]
        pos += 2
    elif fmt == DW_EH_PE_uleb128:
        raw, pos = read_uleb128(buf, pos)
    elif fmt == DW_EH_PE_sleb128:
        raw, pos = read_sleb128(buf, pos)
    else:
        raise ValueError(f"Unsupported DWARF pointer format 0x{enc:02x}")

    if raw == 0 and app in (DW_EH_PE_absptr, DW_EH_PE_pcrel):
        # For omitted/zero values in some encodings keep zero check conservative.
        pass
    if app == DW_EH_PE_absptr:
        val = raw
    elif app == DW_EH_PE_pcrel:
        val = (pcrel_base_va if pcrel_base_va is not None else field_va) + raw
    elif app == DW_EH_PE_datarel:
        val = datarel_base_va + raw
    elif app == DW_EH_PE_funcrel:
        val = funcrel_base_va + raw
    else:
        val = raw
    return val, pos


class Elf64Image:
    """Pure-Python ELF64 section, symbol, and DWARF .eh_frame/.gcc_except_table decoder."""

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

        raw_shdrs = [
            struct.unpack_from("<IIQQQQIIQQ", self.data, e_shoff + i * e_shentsize)
            for i in range(e_shnum)
        ]
        shstr_off = raw_shdrs[e_shstrndx][4]
        shstr_size = raw_shdrs[e_shstrndx][5]
        shstr = self.data[shstr_off : shstr_off + shstr_size]

        self.sections: dict[str, dict[str, Any]] = {}
        self.section_list: list[dict[str, Any]] = []
        for idx, sh in enumerate(raw_shdrs):
            sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, sh_addralign, sh_entsize = sh
            end = shstr.find(b"\x00", sh_name)
            name = shstr[sh_name : end if end != -1 else None].decode("utf-8", "replace")
            sec = {
                "index": idx,
                "name": name,
                "type": sh_type,
                "flags": sh_flags,
                "addr": sh_addr,
                "offset": sh_offset,
                "size": sh_size,
                "link": sh_link,
                "info": sh_info,
                "entsize": sh_entsize,
            }
            self.section_list.append(sec)
            if name:
                self.sections[name] = sec

        self.symbols_by_name: dict[str, list[dict[str, Any]]] = {}
        self._load_symtab(".symtab")

    def section_bytes(self, name: str) -> bytes:
        sec = self.sections[name]
        return self.data[sec["offset"] : sec["offset"] + sec["size"]]

    def _load_symtab(self, sec_name: str) -> None:
        sec = self.sections.get(sec_name)
        if not sec or sec["entsize"] == 0:
            return
        str_sec = self.section_list[sec["link"]]
        strtab = self.data[str_sec["offset"] : str_sec["offset"] + str_sec["size"]]
        raw = self.data[sec["offset"] : sec["offset"] + sec["size"]]
        for off in range(0, len(raw), sec["entsize"]):
            st_name, st_info, st_other, st_shndx, st_value, st_size = struct.unpack_from(
                "<IBBHQQ", raw, off
            )
            end = strtab.find(b"\x00", st_name)
            name = strtab[st_name : end if end != -1 else None].decode("utf-8", "replace")
            if name:
                self.symbols_by_name.setdefault(name, []).append(
                    {
                        "name": name,
                        "value": st_value,
                        "size": st_size,
                        "bind": st_info >> 4,
                        "type": st_info & 0xF,
                        "vis": st_other & 0x3,
                        "shndx": st_shndx,
                    }
                )

    def va_to_file_offset(self, va: int) -> int | None:
        for sec in self.section_list:
            if sec["addr"] != 0 and sec["type"] != 8:  # ignore SHT_NOBITS
                if sec["addr"] <= va < sec["addr"] + sec["size"]:
                    return sec["offset"] + (va - sec["addr"])
        return None

    def read_cstring_at_va(self, va: int) -> str:
        off = self.va_to_file_offset(va)
        if off is None:
            return f"0x{va:x}"
        end = self.data.find(b"\x00", off)
        return self.data[off : end if end != -1 else off + 64].decode("utf-8", "replace")

    def decode_eh_frame_fdes(self) -> list[dict[str, Any]]:
        eh = self.sections.get(".eh_frame")
        if not eh:
            return []
        buf = self.section_bytes(".eh_frame")
        eh_va = eh["addr"]
        cies: dict[int, dict[str, Any]] = {}
        fdes: list[dict[str, Any]] = []
        pos = 0
        while pos + 4 <= len(buf):
            start = pos
            length = struct.unpack_from("<I", buf, pos)[0]
            pos += 4
            if length == 0:
                break
            if length == 0xFFFFFFFF:
                length = struct.unpack_from("<Q", buf, pos)[0]
                pos += 8
            record_end = pos + length
            cie_id = struct.unpack_from("<I", buf, pos)[0]
            p = pos + 4
            if cie_id == 0:
                _ver = buf[p]
                p += 1
                aug_end = buf.find(b"\x00", p)
                aug = buf[p:aug_end].decode("ascii", "replace")
                p = aug_end + 1
                _code_align, p = read_uleb128(buf, p)
                _data_align, p = read_sleb128(buf, p)
                _ret_reg, p = read_uleb128(buf, p)
                fde_enc = DW_EH_PE_absptr
                lsda_enc = DW_EH_PE_omit
                personality_va: int | None = None
                personality_enc = DW_EH_PE_omit
                if aug.startswith("z"):
                    aug_len, p = read_uleb128(buf, p)
                    aug_end_p = p + aug_len
                    for ch in aug[1:]:
                        if ch == "L":
                            lsda_enc = buf[p]
                            p += 1
                        elif ch == "P":
                            personality_enc = buf[p]
                            p += 1
                            personality_va, p = decode_eh_ptr(buf, p, personality_enc, eh_va)
                        elif ch == "R":
                            fde_enc = buf[p]
                            p += 1
                    p = aug_end_p
                cies[start] = {
                    "aug": aug,
                    "fde_enc": fde_enc,
                    "lsda_enc": lsda_enc,
                    "personality_enc": personality_enc,
                    "personality_va": personality_va,
                }
            else:
                cie_off = (pos) - cie_id
                cie = cies.get(cie_off)
                if cie is not None:
                    fde_enc = cie["fde_enc"]
                    pc_begin, p = decode_eh_ptr(buf, p, fde_enc, eh_va)
                    pc_range, p = decode_eh_ptr(
                        buf, p, fde_enc & 0x0F, eh_va  # range is absolute encoding of same format
                    )
                    lsda_va: int | None = None
                    if cie["aug"].startswith("z"):
                        aug_len, p = read_uleb128(buf, p)
                        if cie["lsda_enc"] != DW_EH_PE_omit and aug_len > 0:
                            lsda_va, _ = decode_eh_ptr(buf, p, cie["lsda_enc"], eh_va)
                    if pc_begin is not None and pc_range is not None:
                        fdes.append(
                            {
                                "pc_begin": pc_begin,
                                "pc_end": pc_begin + pc_range,
                                "pc_range": pc_range,
                                "lsda_va": lsda_va,
                                "personality_va": cie["personality_va"],
                                "aug": cie["aug"],
                            }
                        )
            pos = record_end
        return fdes

    def decode_lsda(self, lsda_va: int, func_start: int) -> dict[str, Any]:
        off = self.va_to_file_offset(lsda_va)
        if off is None:
            return {"error": f"lsda VA 0x{lsda_va:x} unmapped"}
        buf = self.data
        pos = off
        lp_start_enc = buf[pos]
        pos += 1
        if lp_start_enc == DW_EH_PE_omit:
            lp_start = func_start
        else:
            val, pos = decode_eh_ptr(buf, pos, lp_start_enc, 0, pcrel_base_va=lsda_va + (pos - off))
            lp_start = val if val is not None else func_start

        ttype_enc = buf[pos]
        pos += 1
        ttype_base_off = None
        if ttype_enc != DW_EH_PE_omit:
            ttype_off, pos = read_uleb128(buf, pos)
            ttype_base_off = pos + ttype_off

        cs_enc = buf[pos]
        pos += 1
        cs_len, pos = read_uleb128(buf, pos)
        cs_end = pos + cs_len
        action_table_start = cs_end

        call_sites: list[dict[str, Any]] = []
        while pos < cs_end:
            cs_start, pos = decode_eh_ptr(buf, pos, cs_enc, 0)
            cs_size, pos = decode_eh_ptr(buf, pos, cs_enc, 0)
            cs_lpad, pos = decode_eh_ptr(buf, pos, cs_enc, 0)
            cs_action, pos = read_uleb128(buf, pos)

            kind = "none"
            ttype_index = None
            if cs_lpad == 0:
                kind = "none"
            elif cs_action == 0:
                kind = "cleanup"
            else:
                apos = action_table_start + cs_action - 1
                ttype_index, _ = read_sleb128(buf, apos)
                if ttype_index == 0:
                    kind = "cleanup"
                elif ttype_index > 0:
                    kind = "catch"
                else:
                    kind = "filter_terminate"

            call_sites.append(
                {
                    "cs_start": cs_start,
                    "cs_len": cs_size,
                    "cs_lpad": cs_lpad,
                    "cs_action": cs_action,
                    "ttype_index": ttype_index,
                    "kind": kind,
                }
            )

        return {
            "lsda_va": f"0x{lsda_va:x}",
            "lp_start": f"0x{lp_start:x}",
            "ttype_enc": f"0x{ttype_enc:02x}",
            "call_site_count": len(call_sites),
            "call_sites": call_sites,
        }


def compile_cxx(
    tools: dict[str, str],
    src: Path,
    out_obj: Path,
    *,
    lto_thin: bool = False,
) -> None:
    cmd = [tools["cxx"]]
    if tools["cxx_driver_mode"] == "clang_x_cpp":
        cmd.extend(["-x", "c++"])
    cmd.extend(["-std=c++17", "-O2", "-fPIC", "-fexceptions", "-c", str(src), "-o", str(out_obj)])
    if lto_thin:
        cmd.append("-flto=thin")
    run_cmd(cmd)


def compile_c17(tools: dict[str, str], src: Path, out_obj: Path) -> None:
    cmd = [tools["gcc"], "-std=c17", "-O2", "-fPIC", "-fexceptions", "-c", str(src), "-o", str(out_obj)]
    run_cmd(cmd)


def parse_readelf_syms(text: str) -> dict[str, dict[str, str]]:
    out: dict[str, dict[str, str]] = {}
    rx = re.compile(
        r"^\s*\d+:\s+([0-9a-fA-F]+)\s+(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)"
    )
    for line in text.splitlines():
        m = rx.match(line)
        if not m:
            continue
        val, sz, typ, bind, vis, ndx, name = m.groups()
        # Strip optional @@SYMVER suffix for canonical lookup while preserving raw
        base_name = name.split("@", 1)[0]
        entry = {
            "raw_name": name,
            "value": val,
            "size": sz,
            "type": typ,
            "bind": bind,
            "vis": vis,
            "ndx": ndx,
        }
        # Prefer defined entry (ndx != UND) if multiple
        prev = out.get(base_name)
        if prev is None or (prev["ndx"] == "UND" and ndx != "UND"):
            out[base_name] = entry
    return out


def analyze_llvm_ir(ll_text: str, fn_names: list[str]) -> dict[str, Any]:
    lines = ll_text.splitlines()
    attr_defs: dict[str, str] = {}
    for line in lines:
        m = re.match(r"^attributes (#\d+) = \{ (.*) \}$", line)
        if m:
            attr_defs[m.group(1)] = m.group(2)

    fns: dict[str, Any] = {}
    for name in fn_names:
        found = None
        for idx, line in enumerate(lines):
            if (line.startswith("define ") or line.startswith("declare ")) and f"@{name}(" in line:
                m_attr = re.search(r"(#\d+)\s*(?:personality|\{|$)", line)
                attr_id = m_attr.group(1) if m_attr else None
                attrs_str = attr_defs.get(attr_id, "") if attr_id else ""
                body_preview = []
                if line.startswith("define "):
                    for k in range(idx, min(len(lines), idx + 35)):
                        body_preview.append(lines[k])
                        if lines[k].strip() == "}":
                            break
                found = {
                    "signature": line,
                    "attr_id": attr_id,
                    "has_nounwind": "nounwind" in attrs_str.split(),
                    "has_uwtable": "uwtable(" in attrs_str or "uwtable" in attrs_str.split(),
                    "has_personality": "personality ptr @rust_eh_personality" in line,
                    "has_filter_lpad": any("filter [0 x ptr] zeroinitializer" in b for b in body_preview),
                    "has_panic_cannot_unwind": any("panic_cannot_unwind" in b for b in body_preview),
                    "has_invoke": any(" invoke " in b for b in body_preview),
                    "attrs": attrs_str,
                }
                break
        fns[name] = found
    return fns


def inspect_abort_unwinding_mir(
    tools: dict[str, str], rs_src: Path, workdir: Path, panic_mode: str, extra_flags: list[str]
) -> dict[str, Any]:
    mir_dir = workdir / f"mir_{panic_mode}"
    mir_dir.mkdir(parents=True, exist_ok=True)
    obj_out = mir_dir / "harness.o"
    cmd = [
        tools["rustc"],
        "--edition=2024",
        "-C",
        "opt-level=2",
        "-C",
        f"panic={panic_mode}",
        "--emit=obj",
        "-Z",
        "dump-mir=AbortUnwindingCalls",
        "-Z",
        f"dump-mir-dir={mir_dir}",
        *extra_flags,
        str(rs_src),
        "-o",
        str(obj_out),
    ]
    run_cmd(cmd)

    targets = [
        "rust_c_unwind_with_guard",
        "rust_c_unwind_no_guard",
        "rust_extern_c_nounwind_with_guard",
    ]
    captured: dict[str, Any] = {}
    for fn in targets:
        before_files = sorted(mir_dir.glob(f"*{fn}*.before.mir"))
        after_files = sorted(mir_dir.glob(f"*{fn}*.after.mir"))
        b_txt = before_files[0].read_text() if before_files else ""
        a_txt = after_files[0].read_text() if after_files else ""
        captured[fn] = {
            "before_bb_count": len(re.findall(r"^\s*bb\d+\b", b_txt, flags=re.MULTILINE)),
            "after_bb_count": len(re.findall(r"^\s*bb\d+\b", a_txt, flags=re.MULTILINE)),
            "before_has_resume": "resume;" in b_txt,
            "after_has_resume": "resume;" in a_txt,
            "after_has_terminate_abi": "terminate(abi);" in a_txt,
            "after_has_unwind_terminate_cleanup": "unwind terminate(cleanup)" in a_txt,
            "after_has_unwind_unreachable": "unwind unreachable" in a_txt,
        }
    return captured


def disassemble_symbol(tools: dict[str, str], elf_path: Path, symbol: str) -> list[str]:
    res = run_cmd(
        [tools["objdump"], "-d", f"--disassemble-symbols={symbol}", str(elf_path)],
        check=False,
    )
    lines = []
    for line in res.stdout.splitlines():
        if re.match(r"^\s*[0-9a-fA-F]+:", line):
            lines.append(line.rstrip())
    return lines


def inspect_binary_fdes(
    elf_path: Path, probe_symbols: list[str]
) -> dict[str, Any]:
    img = Elf64Image(elf_path)
    fdes = img.decode_eh_frame_fdes()
    out: dict[str, Any] = {"total_fdes": len(fdes), "symbols": {}}
    for sym in probe_symbols:
        entries = img.symbols_by_name.get(sym, [])
        if not entries:
            out["symbols"][sym] = {"present_in_symtab": False, "has_fde": False}
            continue
        sv = entries[0]["value"]
        ss = entries[0]["size"]
        matched = [f for f in fdes if f["pc_begin"] <= sv < f["pc_end"]]
        if not matched:
            out["symbols"][sym] = {
                "present_in_symtab": True,
                "va": f"0x{sv:x}",
                "size": ss,
                "has_fde": False,
            }
            continue
        fde = matched[0]
        pers_sym = None
        if fde["personality_va"] is not None:
            # Find symbol near personality_va or check string
            pers_sym = f"0x{fde['personality_va']:x}"
            for sname, slist in img.symbols_by_name.items():
                if any(s["value"] == fde["personality_va"] for s in slist):
                    pers_sym = sname
                    break
        lsda_info = None
        if fde["lsda_va"] is not None:
            lsda_info = img.decode_lsda(fde["lsda_va"], fde["pc_begin"])
        out["symbols"][sym] = {
            "present_in_symtab": True,
            "va": f"0x{sv:x}",
            "size": ss,
            "has_fde": True,
            "fde_range": [f"0x{fde['pc_begin']:x}", f"0x{fde['pc_end']:x}"],
            "personality": pers_sym,
            "lsda": lsda_info,
        }
    return out


def run_visibility_matrix(
    tools: dict[str, str],
    specimens_dir: Path,
    workdir: Path,
) -> dict[str, Any]:
    vis_dir = workdir / "visibility_matrix"
    vis_dir.mkdir(parents=True, exist_ok=True)
    cpp_src = specimens_dir / "ffi_bridge.cpp"
    c17_src = specimens_dir / "ffi_c17_abi.c"
    cdylib_rs = specimens_dir / "rust_cdylib_vis.rs"

    cpp_o = vis_dir / "ffi_bridge.o"
    cpp_lto_o = vis_dir / "ffi_bridge_lto.o"
    c17_o = vis_dir / "ffi_c17_abi.o"
    compile_cxx(tools, cpp_src, cpp_o, lto_thin=False)
    compile_cxx(tools, cpp_src, cpp_lto_o, lto_thin=True)
    compile_c17(tools, c17_src, c17_o)

    watched = [
        "rust_exported_c_unwind_api",
        "rust_custom_export_api",
        "cpp_vis_default_fn",
        "cpp_vis_hidden_fn",
        "gcc_vis_default_fn",
        "gcc_vis_hidden_fn",
        "cpp_thinlto_leaf_mul_add128",
    ]

    def extract_elf_vis(path: Path) -> dict[str, Any]:
        dynsym_txt = run_cmd([tools["readelf"], "--dyn-syms", "-W", str(path)]).stdout
        symtab_txt = run_cmd([tools["readelf"], "-sW", str(path)]).stdout
        dyns = parse_readelf_syms(dynsym_txt)
        syms = parse_readelf_syms(symtab_txt)
        mangled_dyn = [k for k in dyns if "rust_mangled_pub_api" in k]
        mangled_sym = [k for k in syms if "rust_mangled_pub_api" in k]
        rows: dict[str, Any] = {}
        for name in watched:
            rows[name] = {
                "dynsym": dyns.get(name),
                "symtab": syms.get(name),
            }
        rows["rust_mangled_pub_api"] = {
            "dynsym": dyns[mangled_dyn[0]] if mangled_dyn else None,
            "symtab": syms[mangled_sym[0]] if mangled_sym else None,
        }
        return {
            "total_dynsym_defined_globals": sum(
                1 for v in dyns.values() if v["ndx"] != "UND" and v["bind"] in ("GLOBAL", "WEAK")
            ),
            "symbols": rows,
        }

    results: dict[str, Any] = {}

    # 1. Inspect raw C++ and C17 .o visibility before linking
    results["prelink_cpp_obj"] = extract_elf_vis(cpp_o)
    results["prelink_c17_obj"] = extract_elf_vis(c17_o)

    # 2. Pure C++ + C shared library via clang -shared (baseline: C++ STV_DEFAULT leaks into .dynsym, STV_HIDDEN stays local)
    cxx_so = vis_dir / "libcxx_baseline.so"
    run_cmd([tools["cxx"], "-shared", str(cpp_o), str(c17_o), "-o", str(cxx_so)])
    results["clang_shared_so"] = extract_elf_vis(cxx_so)

    # 3. rustc --crate-type=cdylib (default version script)
    cdylib_default = vis_dir / "librust_cdylib_default.so"
    run_cmd([
        tools["rustc"],
        "--edition=2024",
        "--crate-type=cdylib",
        "-C",
        "opt-level=2",
        str(cdylib_rs),
        "-C",
        f"link-arg={cpp_o}",
        "-C",
        f"link-arg={c17_o}",
        "-o",
        str(cdylib_default),
    ])
    results["rustc_cdylib_default"] = extract_elf_vis(cdylib_default)

    # 4. rustc --crate-type=cdylib -Z default-visibility=hidden
    cdylib_hidden = vis_dir / "librust_cdylib_hidden.so"
    run_cmd([
        tools["rustc"],
        "--edition=2024",
        "--crate-type=cdylib",
        "-C",
        "opt-level=2",
        "-Z",
        "default-visibility=hidden",
        str(cdylib_rs),
        "-C",
        f"link-arg={cpp_o}",
        "-C",
        f"link-arg={c17_o}",
        "-o",
        str(cdylib_hidden),
    ])
    results["rustc_cdylib_z_hidden"] = extract_elf_vis(cdylib_hidden)

    # 5. rustc --crate-type=cdylib -C linker-plugin-lto + clang -flto=thin
    cdylib_lto = vis_dir / "librust_cdylib_thinlto.so"
    run_cmd([
        tools["rustc"],
        "--edition=2024",
        "--crate-type=cdylib",
        "-C",
        "opt-level=2",
        "-C",
        "linker-plugin-lto",
        str(cdylib_rs),
        "-C",
        f"link-arg={cpp_lto_o}",
        "-C",
        f"link-arg={c17_o}",
        "-o",
        str(cdylib_lto),
    ])
    results["rustc_cdylib_xlang_thinlto"] = extract_elf_vis(cdylib_lto)
    results["rustc_cdylib_xlang_thinlto"]["disasm_rust_custom_export_api"] = disassemble_symbol(
        tools, cdylib_lto, "rust_custom_export_api"
    )
    results["rustc_cdylib_default"]["disasm_rust_custom_export_api"] = disassemble_symbol(
        tools, cdylib_default, "rust_custom_export_api"
    )

    # 6. rustc --crate-type=rlib inspecting .o object visibility inside archive (default vs -Z default-visibility=hidden)
    def inspect_rlib(extra_vis_flags: list[str], tag: str) -> dict[str, Any]:
        rlib_out = vis_dir / f"libvis_{tag}.rlib"
        run_cmd([
            tools["rustc"],
            "--edition=2024",
            "--crate-type=rlib",
            "-C",
            "opt-level=2",
            "-C",
            "codegen-units=1",
            *extra_vis_flags,
            str(cdylib_rs),
            "-o",
            str(rlib_out),
        ])
        rlib_extract = vis_dir / f"rlib_objs_{tag}"
        rlib_extract.mkdir(exist_ok=True)
        ar_list = run_cmd([tools["ar"], "t", str(rlib_out)]).stdout.splitlines()
        obj_members = [m for m in ar_list if m.endswith(".o")]
        merged_rlib_syms: dict[str, Any] = {}
        if obj_members:
            run_cmd([tools["ar"], "x", str(rlib_out), *obj_members], cwd=rlib_extract)
            for om in obj_members:
                st = parse_readelf_syms(run_cmd([tools["readelf"], "-sW", str(rlib_extract / om)]).stdout)
                for k, v in st.items():
                    if "rust_exported_c_unwind_api" in k or "rust_custom_export_api" in k:
                        merged_rlib_syms[k] = v
                    elif "rust_mangled_pub_api" in k and not k.startswith(".text."):
                        merged_rlib_syms["rust_mangled_pub_api"] = v
        return merged_rlib_syms

    results["rustc_rlib_default_obj_syms"] = inspect_rlib([], "default")
    results["rustc_rlib_z_hidden_obj_syms"] = inspect_rlib(["-Z", "default-visibility=hidden"], "hidden")

    # 7. Probe -C default-linker-libraries=no (default) vs =yes and -Z export-executable-symbols
    def link_args_for(extra: list[str], name: str) -> dict[str, Any]:
        out_bin = vis_dir / name
        res = run_cmd([
            tools["rustc"],
            "--edition=2024",
            "-C",
            "opt-level=2",
            "--print=link-args",
            *extra,
            str(specimens_dir / "rust_ffi_harness.rs"),
            "-C",
            f"link-arg={cpp_o}",
            "-C",
            f"link-arg={c17_o}",
            "-C",
            f"link-arg={tools['libstdcpp']}",
            "-o",
            str(out_bin),
        ])
        link_line = res.stdout.strip()
        vis_info = extract_elf_vis(out_bin)
        return {
            "has_nodefaultlibs": "-nodefaultlibs" in link_line,
            "has_dynamic_list": "--dynamic-list" in link_line,
            "rust_c_unwind_in_dynsym": vis_info["symbols"]["rust_exported_c_unwind_api"]
            if "rust_exported_c_unwind_api" in vis_info["symbols"]
            else None,
            "dynsym_check": parse_readelf_syms(
                run_cmd([tools["readelf"], "--dyn-syms", "-W", str(out_bin)]).stdout
            ).get("rust_c_unwind_with_guard"),
        }

    results["bin_default_linker_libs_no"] = link_args_for([], "bin_def_no")
    results["bin_default_linker_libs_yes"] = link_args_for(
        ["-C", "default-linker-libraries=yes"], "bin_def_yes"
    )
    results["bin_export_exec_syms"] = link_args_for(
        ["-Z", "export-executable-symbols"], "bin_export_syms"
    )

    return results


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--out",
        type=Path,
        default=None,
        help="Optional output JSON path (defaults to stdout)",
    )
    args = parser.parse_args()

    tools = find_tools()
    specimens_dir = Path(__file__).resolve().parent / "specimens"
    for req_file in [
        "ffi_bridge.cpp",
        "ffi_c17_abi.c",
        "rust_ffi_harness.rs",
        "rust_cdylib_vis.rs",
        "rust_staticlib_abort.rs",
        "cpp_main_nocatch.cpp",
    ]:
        if not (specimens_dir / req_file).is_file():
            raise FileNotFoundError(f"Missing specimen {specimens_dir / req_file}")

    rustc_ver = run_cmd([tools["rustc"], "--version", "-v"]).stdout.strip()
    cxx_ver = run_cmd([tools["cxx"], "--version"]).stdout.splitlines()[0].strip()
    gcc_ver = run_cmd([tools["gcc"], "--version"]).stdout.splitlines()[0].strip()
    readelf_ver = run_cmd([tools["readelf"], "--version"]).stdout.splitlines()[0].strip()

    with tempfile.TemporaryDirectory(prefix="cross_lang_ffi_crucible_") as td:
        workdir = Path(td)
        cpp_o = workdir / "ffi_bridge.o"
        cpp_lto_o = workdir / "ffi_bridge_lto.o"
        c17_o = workdir / "ffi_c17_abi.o"

        compile_cxx(tools, specimens_dir / "ffi_bridge.cpp", cpp_o, lto_thin=False)
        compile_cxx(tools, specimens_dir / "ffi_bridge.cpp", cpp_lto_o, lto_thin=True)
        compile_c17(tools, specimens_dir / "ffi_c17_abi.c", c17_o)

        # Inspect MIR AbortUnwindingCalls and LLVM IR across profiles
        mir_audit = {
            "panic_unwind": inspect_abort_unwinding_mir(
                tools, specimens_dir / "rust_ffi_harness.rs", workdir, "unwind", []
            ),
            "panic_abort": inspect_abort_unwinding_mir(
                tools, specimens_dir / "rust_ffi_harness.rs", workdir, "abort", []
            ),
        }

        profile_specs = [
            {
                "name": "panic_unwind_O2",
                "panic": "unwind",
                "extra_flags": [],
                "use_lto_cpp": False,
            },
            {
                "name": "panic_abort_O2",
                "panic": "abort",
                "extra_flags": [],
                "use_lto_cpp": False,
            },
            {
                "name": "panic_abort_no_uwtable_O2",
                "panic": "abort",
                "extra_flags": ["-C", "force-unwind-tables=no"],
                "use_lto_cpp": False,
            },
            {
                "name": "panic_unwind_xlang_thinlto_O2",
                "panic": "unwind",
                "extra_flags": ["-C", "linker-plugin-lto"],
                "use_lto_cpp": True,
            },
        ]

        ir_targets = [
            "rust_c_unwind_with_guard",
            "rust_c_unwind_no_guard",
            "rust_extern_c_nounwind_with_guard",
            "rust_call_cpp_thinlto_leaf",
            "cpp_throw_code",
            "cpp_spill_5gpr_128",
        ]
        fde_probe_syms = [
            "rust_c_unwind_with_guard",
            "rust_c_unwind_no_guard",
            "rust_panic_target",
            "rust_catch_cpp_throw_inner",
            "rust_extern_c_nounwind_with_guard",
            "rust_call_cpp_thinlto_leaf",
            "cpp_throw_code",
            "cpp_try_call_rust",
            "cpp_raii_then_rust_panic",
        ]
        modes = [
            "cell1_cpp_through_rust_c_unwind",
            "cell2_rust_panic_through_cpp_raii",
            "cell3_rust_catch_unwind_on_cpp",
            "cell4a_c_unwind_no_guard",
            "cell5_extern_c_nounwind_throw",
            "i128_abi",
            "xlang_thinlto",
        ]

        profiles_out: dict[str, Any] = {}
        for spec in profile_specs:
            pname = spec["name"]
            pdir = workdir / pname
            pdir.mkdir(parents=True, exist_ok=True)
            exe_path = pdir / "harness"
            ll_path = pdir / "harness.ll"

            emit_ir_flags = (
                ["-C", "force-unwind-tables=no"]
                if "force-unwind-tables=no" in spec["extra_flags"]
                else []
            )
            run_cmd([
                tools["rustc"],
                "--edition=2024",
                "-C",
                "opt-level=2",
                "-C",
                f"panic={spec['panic']}",
                "--emit=llvm-ir",
                *emit_ir_flags,
                str(specimens_dir / "rust_ffi_harness.rs"),
                "-o",
                str(ll_path),
            ])
            ir_summary = analyze_llvm_ir(ll_path.read_text(), ir_targets)

            bridge_obj = cpp_lto_o if spec["use_lto_cpp"] else cpp_o
            run_cmd([
                tools["rustc"],
                "--edition=2024",
                "-C",
                "opt-level=2",
                "-C",
                f"panic={spec['panic']}",
                *spec["extra_flags"],
                str(specimens_dir / "rust_ffi_harness.rs"),
                "-C",
                f"link-arg={bridge_obj}",
                "-C",
                f"link-arg={c17_o}",
                "-C",
                f"link-arg={tools['libstdcpp']}",
                "-o",
                str(exe_path),
            ])

            mode_runs: dict[str, Any] = {}
            for m in modes:
                res = run_cmd([str(exe_path), m], check=False, timeout=20.0)
                trace_events, clean_err = parse_trace_events(res.stderr)
                mode_runs[m] = {
                    "rc": res.returncode,
                    "stdout": scrub_text(res.stdout.strip(), workdir, specimens_dir),
                    "stderr": scrub_text(clean_err.strip(), workdir, specimens_dir),
                    "trace_events": trace_events,
                }

            eh_audit = inspect_binary_fdes(exe_path, fde_probe_syms)
            thinlto_disasm = disassemble_symbol(tools, exe_path, "rust_call_cpp_thinlto_leaf")
            thinlto_calls = [
                line for line in thinlto_disasm if re.search(r"\bcallq?\b", line)
            ]

            profiles_out[pname] = {
                "compile_rc": 0,
                "binary_size_bytes": exe_path.stat().st_size,
                "llvm_ir": ir_summary,
                "eh_frame_audit": eh_audit,
                "thinlto_caller_disasm": thinlto_disasm,
                "thinlto_caller_has_call": len(thinlto_calls) > 0,
                "modes": mode_runs,
            }

        # Disassemble ABI spill functions in C++ and C17 objects for register evidence
        abi_disasm = {
            "cpp_spill_5gpr_128": disassemble_symbol(tools, cpp_o, "cpp_spill_5gpr_128"),
            "gcc_spill_5gpr_128": disassemble_symbol(tools, c17_o, "gcc_spill_5gpr_128"),
            "cpp_unaligned_gpr_128": disassemble_symbol(tools, cpp_o, "cpp_unaligned_gpr_128"),
            "gcc_unaligned_gpr_128": disassemble_symbol(tools, c17_o, "gcc_unaligned_gpr_128"),
        }

        visibility_matrix = run_visibility_matrix(tools, specimens_dir, workdir)

        # Cell 4c: C++ main() (no outer catch!) calling `-C panic=abort` Rust staticlib `extern "C-unwind"`
        c4c_dir = workdir / "cell4c_cpp_main"
        c4c_dir.mkdir(parents=True, exist_ok=True)
        cpp_main_o = c4c_dir / "cpp_main_nocatch.o"
        rs_staticlib_a = c4c_dir / "librust_staticlib_abort.a"
        c4c_exe = c4c_dir / "cpp_main_abort"
        compile_cxx(tools, specimens_dir / "cpp_main_nocatch.cpp", cpp_main_o, lto_thin=False)
        run_cmd([
            tools["rustc"],
            "--edition=2024",
            "-C",
            "opt-level=2",
            "-C",
            "panic=abort",
            str(specimens_dir / "rust_staticlib_abort.rs"),
            "-o",
            str(rs_staticlib_a),
        ])
        run_cmd([
            tools["gcc"],
            str(cpp_main_o),
            str(rs_staticlib_a),
            tools["libstdcpp"],
            "-lpthread",
            "-ldl",
            "-lm",
            "-o",
            str(c4c_exe),
        ])
        c4c_runs = {}
        for arg in ("n", "g"):
            r = run_cmd([str(c4c_exe), arg], check=False, timeout=20.0)
            tev, cerr = parse_trace_events(r.stderr)
            c4c_runs[f"mode_{arg}"] = {
                "rc": r.returncode,
                "stdout": scrub_text(r.stdout.strip(), workdir, specimens_dir),
                "stderr": scrub_text(cerr.strip(), workdir, specimens_dir),
                "trace_events": tev,
            }
        cell4c_cpp_main_abort = {
            "eh_frame_audit": inspect_binary_fdes(
                c4c_exe,
                ["rust_staticlib_c_unwind_with_guard", "rust_staticlib_c_unwind_no_guard", "cpp_throw_nocatch"],
            ),
            "runs": c4c_runs,
        }

    spec_hashes = {}
    for fn in [
        "ffi_bridge.cpp",
        "ffi_c17_abi.c",
        "rust_ffi_harness.rs",
        "rust_cdylib_vis.rs",
        "rust_staticlib_abort.rs",
        "cpp_main_nocatch.cpp",
    ]:
        b = (specimens_dir / fn).read_bytes()
        spec_hashes[fn] = {
            "bytes": len(b),
            "sha256": hashlib.sha256(b).hexdigest(),
        }

    payload = {
        "observed_at": "2026-11-21",
        "toolchains": {
            "rustc": rustc_ver,
            "cxx": cxx_ver,
            "cxx_driver_mode": tools["cxx_driver_mode"],
            "gcc": gcc_ver,
            "readelf": readelf_ver,
            "libstdcpp": Path(tools["libstdcpp"]).name,
        },
        "specimen_hashes": spec_hashes,
        "mir_abort_unwinding_calls": mir_audit,
        "profiles": profiles_out,
        "cell4c_cpp_main_nocatch_staticlib_abort": cell4c_cpp_main_abort,
        "abi_disassembly": abi_disasm,
        "visibility_and_linker_matrix": visibility_matrix,
    }

    text_out = json.dumps(payload, indent=2, ensure_ascii=True, sort_keys=True) + "\n"
    if args.out is not None:
        args.out.parent.mkdir(parents=True, exist_ok=True)
        args.out.write_text(text_out, encoding="utf-8")
    else:
        sys.stdout.write(text_out)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
