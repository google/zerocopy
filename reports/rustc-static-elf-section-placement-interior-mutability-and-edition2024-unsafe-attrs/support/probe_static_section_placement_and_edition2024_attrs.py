#!/usr/bin/env python3
"""Live empirical probe for:
1. Five-category Rust static ELF section placement (.rodata, .data.rel.ro, .data, .bss,
   mutable+reloc .data) under Freeze vs UnsafeCell/Atomic/static mut, PIC vs static reloc
   models, PT_GNU_RELRO / mprotect runtime memory-protection behavior, and cross-section
   flag contamination from `#[unsafe(link_section = ".rodata")]` across GNU ld.bfd and LLD.
2. Edition 2021 vs Edition 2024 #[unsafe(no_mangle)], #[unsafe(export_name)], and
   #[unsafe(link_section)] safety enforcement, cross-edition macro span rules, precedence,
   linkage/export behavior, invalid-target diagnostics, and bit-identical LLVM-IR / ELF emission.
"""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any


RUSTC_BIN = shutil.which("rustc") or str(Path.home() / ".cargo" / "bin" / "rustc")
READELF_BIN = shutil.which("readelf") or "/usr/bin/readelf"


def find_llvm_tools() -> dict[str, str]:
    tools: dict[str, str] = {}
    res = subprocess.run(
        [RUSTC_BIN, "--print", "sysroot"],
        capture_output=True,
        text=True,
        check=True,
    )
    sysroot = Path(res.stdout.strip())
    res_host = subprocess.run(
        [RUSTC_BIN, "-vV"],
        capture_output=True,
        text=True,
        check=True,
    )
    host = ""
    for line in res_host.stdout.splitlines():
        if line.startswith("host:"):
            host = line.split(":", 1)[1].strip()
    tool_dir = sysroot / "lib" / "rustlib" / host / "bin"
    for name in ("llvm-readobj", "llvm-objdump", "llvm-nm", "rust-lld"):
        cand = tool_dir / name
        if cand.is_file():
            tools[name] = str(cand)
        else:
            found = shutil.which(name)
            if found:
                tools[name] = found
    return tools


def run_cmd(cmd: list[str], cwd: Path | None = None) -> subprocess.CompletedProcess[str]:
    return subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        check=False,
    )


def sanitize_text(s: str, tmp_dir: Path) -> str:
    home_str = str(Path.home())
    out = s.replace(str(tmp_dir), "<TMP>").replace(home_str, "<HOME>")
    return out.strip()


def parse_readelf_sections(text: str) -> list[dict[str, Any]]:
    sections: list[dict[str, Any]] = []
    pat = re.compile(
        r"^\s*\[\s*(\d+)\]\s+(\S*)\s+([A-Z0-9_]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+"
        r"([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([WAXMSILOGTCREploxD]*)\s+(\d+)\s+(\d+)\s+(\d+)\s*$"
    )
    for line in text.splitlines():
        m = pat.match(line)
        if m:
            sections.append(
                {
                    "index": int(m.group(1)),
                    "name": m.group(2),
                    "type": m.group(3),
                    "addr_hex": m.group(4),
                    "off_hex": m.group(5),
                    "size_hex": m.group(6),
                    "size": int(m.group(6), 16),
                    "es_hex": m.group(7),
                    "flags": m.group(8),
                    "link": int(m.group(9)),
                    "info": int(m.group(10)),
                    "align": int(m.group(11)),
                }
            )
    return sections


def parse_readelf_symbols(text: str, sections_by_idx: dict[int, dict[str, Any]]) -> dict[str, dict[str, Any]]:
    syms: dict[str, dict[str, Any]] = {}
    pat = re.compile(
        r"^\s*\d+:\s+[0-9a-fA-F]+\s+(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s*(.*)$"
    )
    for line in text.splitlines():
        m = pat.match(line)
        if not m:
            continue
        size, stype, bind, vis, ndx, name = (
            int(m.group(1)),
            m.group(2),
            m.group(3),
            m.group(4),
            m.group(5),
            m.group(6).strip(),
        )
        if not name:
            continue
        sec_info = None
        if ndx.isdigit():
            sec_info = sections_by_idx.get(int(ndx))
        syms[name] = {
            "size": size,
            "type": stype,
            "bind": bind,
            "vis": vis,
            "ndx": ndx,
            "section": sec_info,
        }
    return syms


def parse_readelf_relas(text: str) -> dict[str, list[dict[str, str]]]:
    relas: dict[str, list[dict[str, str]]] = {}
    cur_sec: str | None = None
    hdr_pat = re.compile(r"^Relocation section '([^']+)' at offset")
    row_pat = re.compile(
        r"^\s*([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+(\S+)\s+([0-9a-fA-F]+)\s+(.+)$"
    )
    for line in text.splitlines():
        hm = hdr_pat.match(line.strip())
        if hm:
            cur_sec = hm.group(1)
            relas[cur_sec] = []
            continue
        if cur_sec is not None:
            rm = row_pat.match(line)
            if rm:
                relas[cur_sec].append(
                    {
                        "offset": rm.group(1),
                        "info": rm.group(2),
                        "type": rm.group(3),
                        "sym_value": rm.group(4),
                        "sym_and_addend": rm.group(5).strip(),
                    }
                )
    return relas


def parse_program_headers(text: str) -> list[dict[str, str]]:
    phdrs: list[dict[str, str]] = []
    in_hdr = False
    lines = text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.strip().startswith("Program Headers:"):
            in_hdr = True
            i += 1
            continue
        if in_hdr:
            if line.strip().startswith("Section to Segment mapping:"):
                break
            m = re.match(
                r"^\s*([A-Z0-9_]+)\s+(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+)\s*$",
                line,
            )
            if m and i + 1 < len(lines):
                nxt = lines[i + 1]
                m2 = re.match(
                    r"^\s*(0x[0-9a-fA-F]+)\s+(0x[0-9a-fA-F]+)\s+([RWE ]+?)\s+(0x[0-9a-fA-F]+)\s*$",
                    nxt,
                )
                if m2:
                    phdrs.append(
                        {
                            "type": m.group(1),
                            "offset": m.group(2),
                            "vaddr": m.group(3),
                            "paddr": m.group(4),
                            "filesz": m2.group(1),
                            "memsz": m2.group(2),
                            "flags": m2.group(3).strip(),
                            "align": m2.group(4),
                        }
                    )
                    i += 2
                    continue
        i += 1
    return phdrs


def inspect_object(obj_path: Path, llvm_tools: dict[str, str]) -> dict[str, Any]:
    gnu_sec_res = run_cmd([READELF_BIN, "-SW", str(obj_path)])
    gnu_sym_res = run_cmd([READELF_BIN, "-sW", str(obj_path)])
    gnu_rel_res = run_cmd([READELF_BIN, "-rW", str(obj_path)])
    sections = parse_readelf_sections(gnu_sec_res.stdout)
    sec_by_idx = {s["index"]: s for s in sections}
    symbols = parse_readelf_symbols(gnu_sym_res.stdout, sec_by_idx)
    relocs = parse_readelf_relas(gnu_rel_res.stdout)
    out: dict[str, Any] = {
        "file_sha256": hashlib.sha256(obj_path.read_bytes()).hexdigest(),
        "file_bytes": obj_path.stat().st_size,
        "sections": sections,
        "symbols": symbols,
        "relocations": relocs,
        "readelf_SW": gnu_sec_res.stdout.strip(),
        "readelf_sW": gnu_sym_res.stdout.strip(),
        "readelf_rW": gnu_rel_res.stdout.strip(),
    }
    if "llvm-readobj" in llvm_tools:
        lres = run_cmd([llvm_tools["llvm-readobj"], "--elf-output-style=GNU", "-SW", str(obj_path)])
        out["llvm_readelf_SW"] = lres.stdout.strip()
    return out


def extract_llvm_globals(ll_text: str) -> list[str]:
    return [
        line.strip()
        for line in ll_text.splitlines()
        if line.startswith("@") and (" = " in line)
    ]


def run_group_a_edition_attrs(tmp: Path, llvm_tools: dict[str, str]) -> dict[str, Any]:
    results: dict[str, Any] = {}

    src_bare = """#[no_mangle]
pub static NM_STATIC: u64 = 1;

#[export_name = "custom_exp_sym"]
pub static EXP_STATIC: u64 = 2;

#[link_section = ".custom_ro_sec"]
pub static LS_STATIC: u64 = 3;

#[no_mangle]
pub extern "C" fn nm_fn() -> u64 { 10 }
"""
    src_unsafe = """#[unsafe(no_mangle)]
pub static NM_STATIC: u64 = 1;

#[unsafe(export_name = "custom_exp_sym")]
pub static EXP_STATIC: u64 = 2;

#[unsafe(link_section = ".custom_ro_sec")]
pub static LS_STATIC: u64 = 3;

#[unsafe(no_mangle)]
pub extern "C" fn nm_fn() -> u64 { 10 }
"""

    def compile_pair(
        tag: str,
        src: str,
        edition: str,
        extra_flags: list[str] | None = None,
        crate_type: str = "rlib",
    ) -> dict[str, Any]:
        d = tmp / tag
        d.mkdir(parents=True, exist_ok=True)
        rs = d / "probe.rs"
        rs.write_text(src, encoding="utf-8")
        obj = d / "probe.o"
        ll = d / "probe.ll"
        flags = [
            "--crate-name",
            "attr_probe",
            "--crate-type",
            crate_type,
            "--edition",
            edition,
            "-C",
            "opt-level=2",
        ]
        if extra_flags:
            flags.extend(extra_flags)
        res_obj = run_cmd([RUSTC_BIN, *flags, "--emit=obj", "-o", str(obj), str(rs)])
        entry: dict[str, Any] = {
            "edition": edition,
            "extra_flags": extra_flags or [],
            "obj_rc": res_obj.returncode,
            "obj_stderr": sanitize_text(res_obj.stderr, tmp),
        }
        if res_obj.returncode == 0:
            res_ll = run_cmd([RUSTC_BIN, *flags, "--emit=llvm-ir", "-o", str(ll), str(rs)])
            entry["ll_rc"] = res_ll.returncode
            entry["llvm_ir_globals"] = extract_llvm_globals(ll.read_text(encoding="utf-8"))
            entry["llvm_ir_sha256"] = hashlib.sha256(ll.read_bytes()).hexdigest()
            entry["elf"] = inspect_object(obj, llvm_tools)
        return entry

    results["ed2021_bare"] = compile_pair("a1_ed2021_bare", src_bare, "2021")
    results["ed2021_bare_warn_lint"] = compile_pair(
        "a1b_ed2021_bare_warn", src_bare, "2021", ["-W", "unsafe-attr-outside-unsafe"]
    )
    results["ed2021_bare_forbid_unsafe_code"] = compile_pair(
        "a1c_ed2021_bare_forbid", src_bare, "2021", ["-F", "unsafe-code"]
    )
    results["ed2024_bare_rejected"] = compile_pair("a2_ed2024_bare", src_bare, "2024")
    results["ed2021_unsafe_accepted"] = compile_pair("a3a_ed2021_unsafe", src_unsafe, "2021")
    results["ed2024_unsafe_accepted"] = compile_pair("a3b_ed2024_unsafe", src_unsafe, "2024")
    results["ed2024_unsafe_forbid_unsafe_code"] = compile_pair(
        "a3c_ed2024_unsafe_forbid", src_unsafe, "2024", ["-F", "unsafe-code"]
    )

    g21_b = results["ed2021_bare"]["llvm_ir_globals"]
    g21_u = results["ed2021_unsafe_accepted"]["llvm_ir_globals"]
    g24_u = results["ed2024_unsafe_accepted"]["llvm_ir_globals"]
    results["codegen_equivalence"] = {
        "llvm_globals_identical_2021_bare_vs_2021_unsafe": g21_b == g21_u,
        "llvm_globals_identical_2021_unsafe_vs_2024_unsafe": g21_u == g24_u,
        "llvm_ir_sha256_equal_2021_vs_2024": (
            results["ed2021_unsafe_accepted"]["llvm_ir_sha256"]
            == results["ed2024_unsafe_accepted"]["llvm_ir_sha256"]
        ),
        "obj_sha256_equal_2021_bare_vs_2024_unsafe": (
            results["ed2021_bare"]["elf"]["file_sha256"]
            == results["ed2024_unsafe_accepted"]["elf"]["file_sha256"]
        ),
        "obj_sha256_equal_2021_unsafe_vs_2024_unsafe": (
            results["ed2021_unsafe_accepted"]["elf"]["file_sha256"]
            == results["ed2024_unsafe_accepted"]["elf"]["file_sha256"]
        ),
    }

    results["normal_attr_with_unsafe_rejected"] = compile_pair(
        "a4_normal_unsafe",
        """#[unsafe(used)]
pub static BAD_USED: u64 = 1;

#[unsafe(inline)]
pub fn bad_inline() -> u64 { 1 }
""",
        "2024",
    )

    results["mix_no_mangle_export_both_orders"] = compile_pair(
        "a4_mix_order",
        """#[unsafe(no_mangle)]
#[unsafe(export_name = "exp_wins_first")]
pub static MIX1: u64 = 11;

#[unsafe(export_name = "exp_wins_second")]
#[unsafe(no_mangle)]
pub static MIX2: u64 = 22;
""",
        "2024",
    )

    results["invalid_targets_and_lints"] = {
        "no_mangle_on_const": compile_pair(
            "a4_const_nm",
            "#[unsafe(no_mangle)]\npub const BAD_CONST: u64 = 7;\n",
            "2024",
        ),
        "no_mangle_on_generic_fn": compile_pair(
            "a4_generic_nm",
            "#[unsafe(no_mangle)]\npub fn bad_gen<T>(x: T) -> T { x }\n",
            "2024",
        ),
        "nul_byte_in_export_name": compile_pair(
            "a4_nul_exp",
            "#[unsafe(export_name = \"bad\\0name\")]\npub static BAD_EXP: u64 = 1;\n",
            "2024",
        ),
        "empty_export_name": compile_pair(
            "a4_empty_exp",
            "#[unsafe(export_name = \"\")]\npub static EMPTY_EXP: u64 = 1;\n",
            "2024",
        ),
        "non_ascii_no_mangle": compile_pair(
            "a4_nonascii_nm",
            "#[unsafe(no_mangle)]\npub static αβγ: u64 = 1;\n",
            "2024",
        ),
    }

    # A5: Cross-edition macro span test
    d_mac = tmp / "a5_cross_edition_macro"
    d_mac.mkdir(parents=True, exist_ok=True)
    mac_rs = d_mac / "mac2021.rs"
    mac_rs.write_text(
        """#[macro_export]
macro_rules! def_bare_nm {
    ($name:ident, $val:expr) => {
        #[no_mangle]
        pub static $name: u64 = $val;
    };
}
""",
        encoding="utf-8",
    )
    mac_rlib = d_mac / "libmac2021.rlib"
    r_mac = run_cmd(
        [
            RUSTC_BIN,
            "--crate-name",
            "mac2021",
            "--crate-type",
            "rlib",
            "--edition",
            "2021",
            "-o",
            str(mac_rlib),
            str(mac_rs),
        ]
    )
    use_rs = d_mac / "use2024.rs"
    use_rs.write_text("mac2021::def_bare_nm!(MACRO_ED2021_IN_2024, 99);\n", encoding="utf-8")
    use_o = d_mac / "use2024.o"
    r_use = run_cmd(
        [
            RUSTC_BIN,
            "--crate-name",
            "use2024",
            "--crate-type",
            "rlib",
            "--edition",
            "2024",
            "--extern",
            f"mac2021={mac_rlib}",
            "--emit=obj",
            "-o",
            str(use_o),
            str(use_rs),
        ]
    )
    results["cross_edition_macro_ed2021_in_ed2024"] = {
        "macro_crate_rc": r_mac.returncode,
        "consumer_ed2024_rc": r_use.returncode,
        "consumer_ed2024_stderr": sanitize_text(r_use.stderr, tmp),
        "elf": inspect_object(use_o, llvm_tools) if r_use.returncode == 0 else None,
    }

    # A6: Private visibility + cdylib export/retention interactions
    d_cd = tmp / "a6_priv_cdylib_direct"
    d_cd.mkdir(parents=True, exist_ok=True)
    cd_rs = d_cd / "lib.rs"
    cd_rs.write_text(
        """#[unsafe(no_mangle)]
static PRIV_NM: u64 = 1;

#[unsafe(export_name = "priv_exp")]
static PRIV_EXP: u64 = 2;

#[allow(dead_code)]
#[unsafe(link_section = ".priv_unreferenced_sec")]
static PRIV_LS_ONLY: u64 = 3;

#[used]
#[unsafe(link_section = ".priv_used_sec")]
static PRIV_LS_USED: u64 = 4;
""",
        encoding="utf-8",
    )
    cd_o = d_cd / "lib.o"
    cd_so = d_cd / "libcd.so"
    r_cd_o = run_cmd(
        [RUSTC_BIN, "--crate-name", "priv_cd", "--crate-type", "cdylib", "--edition", "2024", "--emit=obj", "-o", str(cd_o), str(cd_rs)]
    )
    r_cd_so = run_cmd(
        [RUSTC_BIN, "--crate-name", "priv_cd", "--crate-type", "cdylib", "--edition", "2024", "-o", str(cd_so), str(cd_rs)]
    )
    dynsym = run_cmd([READELF_BIN, "--dyn-syms", "-W", str(cd_so)])
    results["private_attr_cdylib_export"] = {
        "obj_rc": r_cd_o.returncode,
        "so_rc": r_cd_so.returncode,
        "obj_elf": inspect_object(cd_o, llvm_tools) if r_cd_o.returncode == 0 else None,
        "cdylib_dynsyms": dynsym.stdout.strip(),
        "cdylib_sections": parse_readelf_sections(run_cmd([READELF_BIN, "-SW", str(cd_so)]).stdout),
    }

    return results


def run_runtime_binary_suite(
    tmp: Path,
    tag: str,
    include_hazard_rodata_section: bool,
) -> dict[str, Any]:
    d_rt = tmp / tag
    d_rt.mkdir(parents=True, exist_ok=True)
    rt_rs = d_rt / "rt_probe.rs"
    hazard_decl = ""
    hazard_match = ""
    if include_hazard_rodata_section:
        hazard_decl = """
#[unsafe(no_mangle)]
#[unsafe(link_section = ".rodata")]
pub static HAZARD_CELL_IN_RODATA: SyncCell<u64> = SyncCell(UnsafeCell::new(555));
"""
        hazard_match = """
        "write_hazard_cell_in_rodata" => {
            unsafe { *HAZARD_CELL_IN_RODATA.0.get() = 777; }
            let v = unsafe { *HAZARD_CELL_IN_RODATA.0.get() };
            println!("HAZARD_SURVIVED:{}", v);
        }
"""

    rt_rs.write_text(
        f"""use core::cell::UnsafeCell;
use core::sync::atomic::{{AtomicU64, Ordering}};

#[repr(transparent)]
pub struct SyncCell<T>(pub UnsafeCell<T>);
unsafe impl<T: Sync> Sync for SyncCell<T> {{}}

#[repr(C)]
pub struct ImmRelocRecord {{
    pub tag: u64,
    pub target: &'static u64,
}}

#[unsafe(no_mangle)]
pub static IMM_SCALAR: u64 = 42;

#[unsafe(no_mangle)]
pub static IMM_ALL_ZERO: [u8; 64] = [0u8; 64];

#[unsafe(no_mangle)]
pub static IMM_RELRO: ImmRelocRecord = ImmRelocRecord {{
    tag: 0xABCD,
    target: &IMM_SCALAR,
}};

#[unsafe(no_mangle)]
pub static CELL_NONZERO: SyncCell<u64> = SyncCell(UnsafeCell::new(7));

#[unsafe(no_mangle)]
pub static CELL_ZERO: SyncCell<u64> = SyncCell(UnsafeCell::new(0));

#[unsafe(no_mangle)]
pub static ATOMIC_ZERO: AtomicU64 = AtomicU64::new(0);

#[unsafe(no_mangle)]
pub static CELL_REL: SyncCell<&'static u64> = SyncCell(UnsafeCell::new(&IMM_SCALAR));
{hazard_decl}

fn main() {{
    let arg = std::env::args().nth(1).unwrap_or_default();
    match arg.as_str() {{
        "check_readonly" => {{
            assert_eq!(IMM_SCALAR, 42);
            assert_eq!(IMM_ALL_ZERO[63], 0);
            assert_eq!(IMM_RELRO.tag, 0xABCD);
            assert_eq!(*IMM_RELRO.target, 42);
            println!("IMM_OK");
        }}
        "write_rodata" => {{
            let p = (&raw const IMM_SCALAR) as *mut u64;
            unsafe {{ p.write_volatile(999); }}
            println!("UNEXPECTED_SURVIVED");
        }}
        "write_rodata_zero" => {{
            let p = (&raw const IMM_ALL_ZERO) as *mut u8;
            unsafe {{ p.write_volatile(1); }}
            println!("UNEXPECTED_SURVIVED");
        }}
        "write_relro" => {{
            let p = (&raw const IMM_RELRO.tag) as *mut u64;
            unsafe {{ p.write_volatile(999); }}
            println!("UNEXPECTED_SURVIVED");
        }}
        "write_cells" => {{
            unsafe {{
                *CELL_NONZERO.0.get() = 88;
                *CELL_ZERO.0.get() = 99;
                *CELL_REL.0.get() = &*CELL_ZERO.0.get();
            }}
            ATOMIC_ZERO.store(123, Ordering::SeqCst);
            let v1 = unsafe {{ *CELL_NONZERO.0.get() }};
            let v2 = unsafe {{ *CELL_ZERO.0.get() }};
            let v3 = ATOMIC_ZERO.load(Ordering::SeqCst);
            let v4 = unsafe {{ **CELL_REL.0.get() }};
            println!("CELLS_OK:{{}}:{{}}:{{}}:{{}}", v1, v2, v3, v4);
        }}{hazard_match}
        _ => std::process::exit(2),
    }}
}}
""",
        encoding="utf-8",
    )

    linker_cases: dict[str, Any] = {}
    modes_to_run = ["check_readonly", "write_rodata", "write_rodata_zero", "write_relro", "write_cells"]
    if include_hazard_rodata_section:
        modes_to_run.append("write_hazard_cell_in_rodata")

    for linker_name, linker_args in [
        ("gnu_ld_bfd", ["-C", "link-arg=-fuse-ld=bfd"]),
        ("rust_lld", ["-C", "link-arg=-fuse-ld=lld"]),
    ]:
        bin_path = d_rt / f"rt_probe_{linker_name}"
        cmd = [
            RUSTC_BIN,
            "--crate-name",
            "rt_probe",
            "--edition",
            "2024",
            "-C",
            "opt-level=2",
            *linker_args,
            "-o",
            str(bin_path),
            str(rt_rs),
        ]
        r_bin = run_cmd(cmd)
        if r_bin.returncode != 0:
            linker_cases[linker_name] = {
                "compile_rc": r_bin.returncode,
                "stderr": sanitize_text(r_bin.stderr, tmp),
            }
            continue
        sec_map = run_cmd([READELF_BIN, "-lW", str(bin_path)]).stdout
        phdrs = parse_program_headers(sec_map)
        bin_secs = parse_readelf_sections(run_cmd([READELF_BIN, "-SW", str(bin_path)]).stdout)
        comment_str = run_cmd([READELF_BIN, "-p", ".comment", str(bin_path)]).stdout.strip()
        modes = {}
        for mode in modes_to_run:
            p = run_cmd([str(bin_path), mode])
            modes[mode] = {
                "rc": p.returncode,
                "stdout": p.stdout.strip(),
                "stderr": sanitize_text(p.stderr, tmp),
            }
        linker_cases[linker_name] = {
            "compile_rc": 0,
            "comment_section": comment_str,
            "program_headers": phdrs,
            "relevant_sections": [
                s for s in bin_secs if s["name"] in (".rodata", ".data.rel.ro", ".data", ".bss", ".tdata", ".tbss")
            ],
            "readelf_lW": sec_map.strip(),
            "runtime_modes": modes,
        }
    return linker_cases


def run_group_b_five_category_sections(tmp: Path, llvm_tools: dict[str, str]) -> dict[str, Any]:
    results: dict[str, Any] = {}

    src_5cat = """use core::cell::UnsafeCell;
use core::sync::atomic::AtomicU64;

#[repr(transparent)]
pub struct SyncCell<T>(pub UnsafeCell<T>);
unsafe impl<T: Sync> Sync for SyncCell<T> {}

// Cat 1: Immutable non-zero scalar -> .rodata (PROGBITS, A)
#[unsafe(no_mangle)]
pub static CAT1_IMM_SCALAR: u64 = 42;

// Cat 2: Immutable all-zero array -> .rodata (PROGBITS, A), NOT .bss!
#[unsafe(no_mangle)]
pub static CAT2_IMM_ALL_ZERO: [u8; 64] = [0u8; 64];

// Cat 3: Immutable static with pointer relocation -> PIC: .data.rel.ro (PROGBITS, WA) + .rela.data.rel.ro
//                                                   Static: .rodata (PROGBITS, A) + .rela.rodata
#[repr(C)]
pub struct ImmRelocRecord {
    pub tag: u64,
    pub target: &'static u64,
}

#[unsafe(no_mangle)]
pub static CAT3_IMM_WITH_RELOC: ImmRelocRecord = ImmRelocRecord {
    tag: 0xABCD,
    target: &CAT1_IMM_SCALAR,
};

// Cat 4: Interior-mutable non-zero (Atomic + UnsafeCell) -> .data (PROGBITS, WA)
#[unsafe(no_mangle)]
pub static CAT4A_ATOMIC_NONZERO: AtomicU64 = AtomicU64::new(7);

#[unsafe(no_mangle)]
pub static CAT4B_UNSAFECELL_NONZERO: SyncCell<u64> = SyncCell(UnsafeCell::new(0x1122334455667788));

// Cat 5: Interior-mutable all-zero (Atomic + UnsafeCell) -> .bss (NOBITS, WA)
#[unsafe(no_mangle)]
pub static CAT5A_ATOMIC_ZERO: AtomicU64 = AtomicU64::new(0);

#[unsafe(no_mangle)]
pub static CAT5B_UNSAFECELL_ZERO: SyncCell<u64> = SyncCell(UnsafeCell::new(0));

// Cat 6: Interior-mutable with pointer relocation -> .data (PROGBITS, WA) + .rela.data (NEVER .data.rel.ro!)
#[unsafe(no_mangle)]
pub static CAT6_UNSAFECELL_WITH_RELOC: SyncCell<&'static u64> = SyncCell(UnsafeCell::new(&CAT1_IMM_SCALAR));

// Cat 7: static mut (nonzero & zero) -> .data / .bss
#[unsafe(no_mangle)]
pub static mut CAT7A_STATIC_MUT_NONZERO: u64 = 99;

#[unsafe(no_mangle)]
pub static mut CAT7B_STATIC_MUT_ZERO: u64 = 0;

// Cat 8: Custom link_section overrides on immutable vs interior-mutable statics
#[unsafe(no_mangle)]
#[unsafe(link_section = ".custom_sec_imm")]
pub static CAT8A_LINKSEC_IMM: u64 = 123;

#[unsafe(no_mangle)]
#[unsafe(link_section = ".custom_sec_mut")]
pub static CAT8B_LINKSEC_CELL: SyncCell<u64> = SyncCell(UnsafeCell::new(456));

#[unsafe(no_mangle)]
#[unsafe(link_section = ".bss.custom_imm")]
pub static CAT8C_LINKSEC_DOT_BSS_IMM: u64 = 0;

#[unsafe(no_mangle)]
#[unsafe(link_section = ".rodata")]
pub static CAT8D_LINKSEC_CELL_IN_RODATA: SyncCell<u64> = SyncCell(UnsafeCell::new(789));
"""

    for reloc_model in ("pic", "static"):
        d = tmp / f"b_reloc_{reloc_model}"
        d.mkdir(parents=True, exist_ok=True)
        rs = d / "sec5.rs"
        rs.write_text(src_5cat, encoding="utf-8")
        obj = d / "sec5.o"
        ll = d / "sec5.ll"
        flags = [
            "--crate-name",
            "sec5",
            "--crate-type",
            "rlib",
            "--edition",
            "2024",
            "-C",
            "opt-level=2",
            "-C",
            f"relocation-model={reloc_model}",
        ]
        r_obj = run_cmd([RUSTC_BIN, *flags, "--emit=obj", "-o", str(obj), str(rs)])
        r_ll = run_cmd([RUSTC_BIN, *flags, "--emit=llvm-ir", "-o", str(ll), str(rs)])
        results[f"reloc_model_{reloc_model}"] = {
            "obj_rc": r_obj.returncode,
            "ll_rc": r_ll.returncode,
            "llvm_ir_globals": extract_llvm_globals(ll.read_text(encoding="utf-8")) if r_ll.returncode == 0 else [],
            "elf": inspect_object(obj, llvm_tools) if r_obj.returncode == 0 else None,
        }

    # Check nonzero static forced into .bss via #[unsafe(link_section = ".bss")] and ".bss.custom_nz"
    bss_nz = {}
    for secname in (".bss", ".bss.custom_nz"):
        d_bss = tmp / f"b_bss_{secname.strip('.').replace('.', '_')}"
        d_bss.mkdir(parents=True, exist_ok=True)
        rs_bss = d_bss / "bss_nz.rs"
        rs_bss.write_text(
            f'#[unsafe(no_mangle)]\n#[unsafe(link_section = "{secname}")]\npub static NZ_IN_BSS: u64 = 0xDEAD_BEEF;\n',
            encoding="utf-8",
        )
        r_bss = run_cmd([RUSTC_BIN, "--crate-name", "bss_nz", "--crate-type", "rlib", "--edition", "2024", "--emit=obj", "-o", str(d_bss / "bss_nz.o"), str(rs_bss)])
        bss_nz[secname] = {"rc": r_bss.returncode, "stderr": sanitize_text(r_bss.stderr, tmp)}
    results["nonzero_in_bss_rejected"] = bss_nz

    results["linked_pie_clean"] = run_runtime_binary_suite(tmp, "b_rt_clean", False)
    results["linked_pie_with_rodata_cell_hazard"] = run_runtime_binary_suite(tmp, "b_rt_hazard", True)
    return results


def main() -> int:
    support_dir = Path(__file__).resolve().parent
    out_path = support_dir / "probe_results.json"

    llvm_tools = find_llvm_tools()
    rustc_v = run_cmd([RUSTC_BIN, "-vV"]).stdout.strip()
    readelf_v = run_cmd([READELF_BIN, "--version"]).stdout.splitlines()[0].strip()

    with tempfile.TemporaryDirectory(prefix="rustc_static_sec_probe_") as tmp_raw:
        tmp = Path(tmp_raw)
        report = {
            "rustc_verbose_version": rustc_v,
            "readelf_version": readelf_v,
            "llvm_tools_found": sorted(llvm_tools.keys()),
            "group_a_edition_2024_unsafe_attrs": run_group_a_edition_attrs(tmp, llvm_tools),
            "group_b_static_five_category_sections": run_group_b_five_category_sections(tmp, llvm_tools),
        }

    out_path.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")

    for label in ("linked_pie_clean", "linked_pie_with_rodata_cell_hazard"):
        print(f"=== {label} ===")
        suite = report["group_b_static_five_category_sections"][label]
        for lname, linfo in suite.items():
            if linfo.get("compile_rc") != 0:
                print(f"  {lname}: compile_rc={linfo.get('compile_rc')}")
                continue
            ro = [s for s in linfo["relevant_sections"] if s["name"] == ".rodata"]
            print(f"  {lname}: .rodata={ro}")
            for mode, mres in linfo["runtime_modes"].items():
                print(f"    {mode}: rc={mres['rc']} out={mres['stdout']!r}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
