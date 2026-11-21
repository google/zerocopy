#!/usr/bin/env python3
"""Executable probes for Cross-Language LTO (-C linker-plugin-lto), fat LTO objects
(.llvm.lto / SHT_LLVM_LTO), GCC GIMPLE LTO (.gnu.lto_* / __gnu_lto_slim),
normal rustc .rlib embedded .llvmbc vs raw bitcode (BC\\xc0\\xde / 0x0B17C0DE),
and a fail-closed linker-input bitcode/IR detector.
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


BITCODE_RAW_MAGIC = b"BC\xc0\xde"          # 42 43 c0 de
BITCODE_WRAPPER_MAGIC = b"\xde\xc0\x17\x0b" # 0x0B17C0DE little-endian
AR_MAGIC = b"!<arch>\n"
THIN_AR_MAGIC = b"!<thin>\n"
ELF_MAGIC = b"\x7fELF"
SHT_LLVM_LTO = 0x6FFF4C0C


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


def inspect_elf_bytes(data: bytes, label: str) -> dict:
    """Minimal standalone ELF64/32 section & symbol-table scanner for LTO/bitcode detection."""
    if not data.startswith(ELF_MAGIC) or len(data) < 64:
        return {"kind": "not_elf"}
    ei_class = data[4]  # 1=32, 2=64
    ei_data = data[5]   # 1=LE, 2=BE
    endian = "<" if ei_data == 1 else ">"
    if ei_class != 2:
        return {"kind": "elf32_unscanned"}
    e_shoff, = struct.unpack_from(endian + "Q", data, 40)
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from(endian + "HHH", data, 58)
    if e_shoff == 0 or e_shnum == 0 or e_shstrndx >= e_shnum:
        return {"kind": "elf64", "sections": []}
    shstr_off = e_shoff + e_shstrndx * e_shentsize
    _, _, _, _, shstr_file_off, shstr_size = struct.unpack_from(endian + "IIQQQQ", data, shstr_off)
    shstr = data[shstr_file_off : shstr_file_off + shstr_size]

    def read_cstr(tbl: bytes, off: int) -> str:
        end = tbl.find(b"\x00", off)
        return tbl[off:end].decode("utf-8", errors="replace") if end != -1 else tbl[off:].decode("utf-8", errors="replace")

    sections = []
    symtab_sec = None
    strtab_sec = None
    sh_entries = []
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type, sh_flags, sh_addr, sh_offset, sh_size, sh_link, sh_info, _, sh_entsize = struct.unpack_from(
            endian + "IIQQQQIIQQ", data, off
        )
        name = read_cstr(shstr, sh_name)
        sh_entries.append((name, sh_type, sh_flags, sh_offset, sh_size, sh_link, sh_entsize))
        sections.append({"name": name, "type_hex": hex(sh_type), "size": sh_size})
        if sh_type == 2:  # SHT_SYMTAB
            symtab_sec = (sh_offset, sh_size, sh_link, sh_entsize)

    lto_marker_syms = []
    if symtab_sec:
        s_off, s_size, s_link, s_ent = symtab_sec
        _, _, _, st_off, st_size, _, _ = sh_entries[s_link]
        strtab = data[st_off : st_off + st_size]
        if s_ent >= 24:
            for pos in range(s_off, s_off + s_size, s_ent):
                st_name, = struct.unpack_from(endian + "I", data, pos)
                sname = read_cstr(strtab, st_name)
                if sname.startswith("__gnu_lto_"):
                    lto_marker_syms.append(sname)

    has_llvmbc = any(s["name"] == ".llvmbc" for s in sections)
    has_llvm_lto = any(s["name"] == ".llvm.lto" or s["type_hex"] == hex(SHT_LLVM_LTO) for s in sections)
    gnu_lto_secs = [s["name"] for s in sections if s["name"].startswith(".gnu.lto_")]
    has_text = any(s["name"] == ".text" or s["name"].startswith(".text.") for s in sections)

    return {
        "kind": "elf64",
        "label": label,
        "has_text": has_text,
        "has_llvmbc_section": has_llvmbc,
        "has_llvm_lto_section": has_llvm_lto,
        "gnu_lto_sections_count": len(gnu_lto_secs),
        "gnu_lto_sections_sample": gnu_lto_secs[:5],
        "gnu_lto_marker_symbols": sorted(set(lto_marker_syms)),
    }


def iter_ar_members(path: pathlib.Path) -> list[tuple[str, bytes]]:
    """Iterates standard !<arch> and thin !<thin> archive members."""
    raw = path.read_bytes()
    is_thin = raw.startswith(THIN_AR_MAGIC)
    if not (raw.startswith(AR_MAGIC) or is_thin):
        raise ValueError(f"Not an ar archive: {path}")
    pos = 8
    long_names = b""
    members = []
    while pos + 60 <= len(raw):
        hdr = raw[pos : pos + 60]
        pos += 60
        name_raw = hdr[0:16].decode("ascii", errors="replace").strip()
        size = int(hdr[48:58].decode("ascii").strip())
        if name_raw in ("/", "/SYM64/"):
            pos += size + (size & 1)
            continue
        if name_raw == "//":
            long_names = raw[pos : pos + size]
            pos += size + (size & 1)
            continue
        if name_raw.startswith("/") and name_raw[1:].isdigit():
            off = int(name_raw[1:])
            end = long_names.find(b"/\n", off)
            if end == -1:
                end = long_names.find(b"\n", off)
            name = long_names[off:end].decode("utf-8", errors="replace").rstrip("/")
        else:
            name = name_raw.rstrip("/")

        if is_thin:
            ext_path = (path.parent / name).resolve()
            payload = ext_path.read_bytes() if ext_path.is_file() else b""
        else:
            payload = raw[pos : pos + size]
            pos += size + (size & 1)
        members.append((name, payload))
    return members


def scan_artifact_fail_closed(path: pathlib.Path, linker_argv: list[str] | None = None, allow_inactive_llvmbc: bool = False) -> dict:
    """Fail-closed bitcode/IR detector for machine-code FFI verifiers.
    Returns verdict='ACCEPT' iff zero raw bitcode, bitcode wrappers, fat LLVM LTO,
    GCC GIMPLE LTO, or LTO-activating linker flags are present.
    """
    findings = []
    argv = linker_argv or []
    for flag in argv:
        if any(
            flag == f or flag.startswith(f + "=") or flag.startswith("-Wl," + f)
            for f in ("-plugin", "--plugin", "-plugin-opt", "--fat-lto-objects", "-flto")
        ):
            findings.append({"reason": "lto_linker_flag", "flag": flag})

    def inspect_blob(blob: bytes, label: str) -> None:
        if blob.startswith(BITCODE_RAW_MAGIC):
            findings.append({"reason": "raw_llvm_bitcode", "magic": blob[:8].hex(), "member": label})
        elif blob.startswith(BITCODE_WRAPPER_MAGIC):
            findings.append({"reason": "llvm_bitcode_wrapper", "magic": blob[:8].hex(), "member": label})
        elif blob.startswith(ELF_MAGIC):
            info = inspect_elf_bytes(blob, label)
            if info.get("has_llvm_lto_section"):
                findings.append({"reason": "fat_llvm_lto_section", "section": ".llvm.lto", "member": label})
            if info.get("gnu_lto_sections_count", 0) > 0 or info.get("gnu_lto_marker_symbols"):
                findings.append({
                    "reason": "gcc_gimple_lto",
                    "sections_count": info.get("gnu_lto_sections_count", 0),
                    "symbols": info.get("gnu_lto_marker_symbols", []),
                    "member": label,
                })
            if info.get("has_llvmbc_section") and not allow_inactive_llvmbc:
                findings.append({"reason": "embedded_llvmbc_section", "section": ".llvmbc", "member": label})

    raw = path.read_bytes()
    if raw.startswith(AR_MAGIC) or raw.startswith(THIN_AR_MAGIC):
        for mname, payload in iter_ar_members(path):
            inspect_blob(payload, f"{path.name}({mname})")
    else:
        inspect_blob(raw, path.name)

    return {
        "artifact": path.name,
        "magic_hex": raw[:8].hex(),
        "verdict_strict": "ACCEPT" if not findings else "REJECT",
        "findings": findings,
    }


def probe_3_bitcode_taxonomy_and_fat_lto(toolchain: str) -> dict:
    with tempfile.TemporaryDirectory(prefix="probe3_") as td:
        root = pathlib.Path(td)
        sysroot = pathlib.Path(run(["rustc", f"+{toolchain}", "--print", "sysroot"]).stdout.strip())
        rust_lld = sysroot / "lib/rustlib/x86_64-unknown-linux-gnu/bin/rust-lld"

        c_src = root / "ffi_math.c"
        c_src.write_text(
            "#include <stdint.h>\n"
            "int32_t c_double_add(int32_t x, int32_t y) { return x * 2 + y; }\n"
        )
        rs_lib = root / "rlib_demo.rs"
        rs_lib.write_text(
            'extern "C" { fn c_double_add(x: i32, y: i32) -> i32; }\n'
            '#[no_mangle] pub extern "C" fn rust_entry(x: i32) -> i32 {\n'
            '    unsafe { c_double_add(x, 5) }\n'
            '}\n'
        )

        # Build the 7 distinct artifact classes
        c_native_o = root / "c_native.o"
        run(["gcc", "-O2", "-fPIC", "-c", str(c_src), "-o", str(c_native_o)])

        c_clang_thin_o = root / "c_clang_thin.o"
        run(["clang-19", "--target=x86_64-unknown-linux-gnu", "-O2", "-fPIC", "-flto=thin", "-c", str(c_src), "-o", str(c_clang_thin_o)])

        c_clang_fat_o = root / "c_clang_fat.o"
        run(["clang-19", "--target=x86_64-unknown-linux-gnu", "-O2", "-fPIC", "-flto=thin", "-ffat-lto-objects", "-c", str(c_src), "-o", str(c_clang_fat_o)])

        c_gcc_slim_o = root / "c_gcc_slim.o"
        run(["gcc", "-O2", "-fPIC", "-flto", "-fno-fat-lto-objects", "-c", str(c_src), "-o", str(c_gcc_slim_o)])

        c_gcc_fat_o = root / "c_gcc_fat.o"
        run(["gcc", "-O2", "-fPIC", "-flto", "-ffat-lto-objects", "-c", str(c_src), "-o", str(c_gcc_fat_o)])

        # Archive wrapping a thin-LTO object + a thin archive pointing to a bitcode object
        c_thin_ar = root / "libthin_bitcode.a"
        run(["ar", "rcsT", str(c_thin_ar), str(c_clang_thin_o)])

        # Synthetic LLVM bitcode wrapper (0x0B17C0DE header wrapping c_clang_thin.o bitcode)
        raw_bc = c_clang_thin_o.read_bytes()
        bc_wrap_o = root / "c_wrapped_bc.o"
        # Header: magic(0x0B17C0DE), version(0), offset(20), size(len), cputype(0)
        bc_wrap_o.write_bytes(struct.pack("<5I", 0x0B17C0DE, 0, 20, len(raw_bc), 0) + raw_bc)

        # Rust rlibs: (a) default (-C embed-bitcode=yes), (b) -C embed-bitcode=no, (c) -C linker-plugin-lto
        rlib_default = root / "libr_default.rlib"
        rlib_no_bc = root / "libr_no_embed_bc.rlib"
        rlib_xlto = root / "libr_xlto.rlib"
        run(["rustc", f"+{toolchain}", "-O", "--crate-type=rlib", str(rs_lib), "-o", str(rlib_default)])
        run(["rustc", f"+{toolchain}", "-O", "--crate-type=rlib", "-C", "embed-bitcode=no", str(rs_lib), "-o", str(rlib_no_bc)])
        run(["rustc", f"+{toolchain}", "-O", "--crate-type=rlib", "-C", "linker-plugin-lto", str(rs_lib), "-o", str(rlib_xlto)])

        # Scan all 10 artifacts with strict detector (rejecting even .llvmbc) AND with allow_inactive_llvmbc=True
        artifacts = [
            c_native_o,
            rlib_no_bc,
            rlib_default,
            rlib_xlto,
            c_clang_thin_o,
            c_thin_ar,
            bc_wrap_o,
            c_clang_fat_o,
            c_gcc_slim_o,
            c_gcc_fat_o,
        ]
        scan_matrix = []
        for art in artifacts:
            strict = scan_artifact_fail_closed(art, allow_inactive_llvmbc=False)
            relaxed_llvmbc = scan_artifact_fail_closed(art, allow_inactive_llvmbc=True)
            scan_matrix.append({
                "artifact": art.name,
                "magic_hex": strict["magic_hex"],
                "verdict_strict_no_llvmbc": strict["verdict_strict"],
                "verdict_allowing_inactive_llvmbc": relaxed_llvmbc["verdict_strict"],
                "strict_reasons": [f["reason"] for f in strict["findings"]],
                "findings_detail": strict["findings"][:3],
            })

        # CRITICAL LIVE DEMO: Link the EXACT SAME fat-LTO C object (c_clang_fat.o) + rlib_xlto
        # with -u rust_entry so rust-lld actually extracts rust_entry from the .rlib!
        # 1) WITHOUT --fat-lto-objects -> rust-lld uses native .text from c_clang_fat.o -> FFI call survives!
        # 2) WITH --fat-lto-objects    -> rust-lld discards native .text, reads .llvm.lto bitcode, INLINES across Rust/C!
        so_no_fat = root / "out_no_fat_flag.so"
        so_with_fat = root / "out_with_fat_flag.so"
        run([str(rust_lld), "-flavor", "gnu", "-shared", "-u", "rust_entry", "--no-fat-lto-objects", str(rlib_xlto), str(c_clang_fat_o), "-o", str(so_no_fat)])
        run([str(rust_lld), "-flavor", "gnu", "-shared", "-u", "rust_entry", "--fat-lto-objects", str(rlib_xlto), str(c_clang_fat_o), "-o", str(so_with_fat)])

        def disasm_fn(so: pathlib.Path, fn: str) -> list[str]:
            txt = run(["llvm-objdump", "-d", f"--disassemble-symbols={fn}", str(so)]).stdout
            return [ln.strip() for ln in txt.splitlines() if ln.strip() and not ln.startswith(str(so)) and not ln.startswith("Disassembly")]

        dis_no_fat = disasm_fn(so_no_fat, "rust_entry")
        dis_with_fat = disasm_fn(so_with_fat, "rust_entry")

        # Also test that rust-lld accepts the 0x0B17C0DE bitcode wrapper directly as LTO input!
        so_wrap = root / "out_wrapped_bc.so"
        wrap_link = run([str(rust_lld), "-flavor", "gnu", "-shared", "-u", "rust_entry", str(rlib_xlto), str(bc_wrap_o), "-o", str(so_wrap)], check=False)
        dis_wrap = disasm_fn(so_wrap, "rust_entry") if wrap_link.returncode == 0 else []

        # Test what happens when rust-lld receives GCC slim LTO (no native .text, only .gnu.lto_*)
        so_gcc_slim = root / "out_gcc_slim.so"
        gcc_slim_lld = run([str(rust_lld), "-flavor", "gnu", "-shared", "-u", "rust_entry", "--no-undefined", str(rlib_no_bc), str(c_gcc_slim_o), "-o", str(so_gcc_slim)], check=False)

        # Test GCC fat LTO with GNU ld + gcc driver (-flto vs -fno-lto)
        c_main = root / "main_gcc.c"
        c_main.write_text("#include <stdio.h>\nint c_double_add(int,int);\nint main(void){printf(\"%d\\n\", c_double_add(10,5));}\n")
        gcc_slim_with_driver = run(["gcc", "-O2", "-flto", str(c_main), str(c_gcc_slim_o), "-o", str(root / "gcc_slim_ok")], check=False)

        return {
            "toolchain": toolchain,
            "scan_matrix": scan_matrix,
            "fat_lto_flag_divergence": {
                "without_fat_lto_flag_disasm": dis_no_fat,
                "without_fat_lto_calls_or_jumps_c_double_add": any("c_double_add" in ln or "jmp" in ln or "call" in ln for ln in dis_no_fat),
                "with_fat_lto_flag_disasm": dis_with_fat,
                "with_fat_lto_inlined_completely": not any("c_double_add" in ln or "jmp" in ln or "call" in ln for ln in dis_with_fat),
            },
            "bitcode_wrapper_0x0b17c0de_accepted_by_rust_lld": {
                "returncode": wrap_link.returncode,
                "inlined_disasm": dis_wrap,
            },
            "gcc_slim_lto_in_rust_lld": {
                "returncode": gcc_slim_lld.returncode,
                "stderr_excerpt": gcc_slim_lld.stderr.strip().splitlines()[:4],
            },
            "gcc_slim_lto_in_gcc_flto_driver_rc": gcc_slim_with_driver.returncode,
        }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--toolchains", nargs="+", default=["1.99.1", "nightly-2026-06-01"])
    parser.add_argument("--json-out", type=pathlib.Path)
    args = parser.parse_args()

    out = {tc: probe_3_bitcode_taxonomy_and_fat_lto(tc) for tc in args.toolchains}
    rendered = json.dumps(out, indent=2)
    if args.json_out:
        args.json_out.write_text(rendered + "\n")
    print(rendered)


if __name__ == "__main__":
    main()
