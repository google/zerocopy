#!/usr/bin/env python3
"""Empirical rustc probe for DWARF v5 split debuginfo (thorin .dwp),
wrapping-niche enum DISCR_BEGIN/DISCR_END inversion vs. native DWARF,
.debug_gdb_scripts executable .text mutation, #![debugger_visualizer]
deduplication, coroutine __state encoding, and #[collapse_debuginfo].

All measurements are executed live against the installed rustc toolchain;
no benchmark or compiler-output metrics are hardcoded.
"""

from __future__ import annotations

import glob
import hashlib
import json
import os
import pathlib
import re
import shutil
import struct
import subprocess
import sys
import tempfile
from typing import Any


def find_rustc() -> str:
    env_rustc = os.environ.get("RUSTC")
    if env_rustc and os.path.isfile(env_rustc):
        return env_rustc
    found = shutil.which("rustc")
    if found:
        return found
    candidates = sorted(
        glob.glob(os.path.expanduser("~/.rustup/toolchains/*/bin/rustc"))
    )
    if candidates:
        return candidates[-1]
    raise RuntimeError("rustc not found in PATH or ~/.rustup/toolchains")


def find_tool(name: str, rustc_path: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    toolchain_root = pathlib.Path(rustc_path).resolve().parent.parent
    lib_bins = glob.glob(str(toolchain_root / "lib/rustlib/*/bin" / name))
    if lib_bins:
        return lib_bins[0]
    raise RuntimeError(f"required tool {name!r} not found")


def run(
    cmd: list[str],
    *,
    cwd: str | pathlib.Path | None = None,
    check: bool = True,
    env: dict[str, str] | None = None,
) -> subprocess.CompletedProcess[str]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
        check=False,
        env=env,
    )
    if check and proc.returncode != 0:
        raise RuntimeError(
            f"Command failed (rc={proc.returncode}): {cmd}\nSTDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
        )
    return proc


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: pathlib.Path) -> str:
    return sha256_bytes(path.read_bytes())


def scrub(text: str, replacements: list[tuple[str, str]]) -> str:
    out = text
    for old, new in replacements:
        if old:
            out = out.replace(old, new)
    return out


def parse_elf64_sections(data: bytes) -> dict[str, bytes]:
    """Read raw section contents from a little-endian 64-bit ELF file."""
    if len(data) < 64 or data[:4] != b"\x7fELF" or data[4] != 2 or data[5] != 1:
        raise ValueError("not an ELF64 little-endian binary")
    e_shoff = struct.unpack_from("<Q", data, 40)[0]
    e_shentsize, e_shnum, e_shstrndx = struct.unpack_from("<HHH", data, 58)
    if e_shoff == 0 or e_shnum == 0:
        return {}
    shstr_hdr_off = e_shoff + e_shstrndx * e_shentsize
    shstr_off, shstr_size = struct.unpack_from("<QQ", data, shstr_hdr_off + 24)
    shstrtab = data[shstr_off : shstr_off + shstr_size]

    sections: dict[str, bytes] = {}
    for i in range(e_shnum):
        off = e_shoff + i * e_shentsize
        sh_name, sh_type = struct.unpack_from("<II", data, off)
        sh_offset, sh_size = struct.unpack_from("<QQ", data, off + 24)
        end = shstrtab.find(b"\x00", sh_name)
        name = shstrtab[sh_name:end].decode("utf-8", errors="replace")
        if sh_type == 8:  # SHT_NOBITS
            sections[name] = b""
        else:
            sections[name] = data[sh_offset : sh_offset + sh_size]
    return sections


def parse_cu_index_unit_count(cu_index_bytes: bytes) -> dict[str, int]:
    """Parse DWARF v4/v5 .debug_cu_index header (version, columns, unit_count, slot_count)."""
    if len(cu_index_bytes) < 16:
        return {"version": 0, "columns": 0, "unit_count": 0, "slot_count": 0}
    # DWARF v5 uses u16 version + u16 padding; DWARF v4 (GNU split DWARF v2) uses u32 version.
    # Both have little-endian version in the first 2 bytes (2 or 5) and padding 0 in bytes 2..4.
    version_u16, pad, columns, unit_count, slot_count = struct.unpack_from(
        "<HHIII", cu_index_bytes, 0
    )
    return {
        "version": version_u16,
        "padding": pad,
        "columns": columns,
        "unit_count": unit_count,
        "slot_count": slot_count,
    }


def natvis_in_range(x: int, begin: int, end: int) -> bool:
    """Exact expression from src/etc/natvis/intrinsic.natvis:306."""
    if begin <= end:
        return begin <= x <= end
    return x >= begin or x <= end


def probe_1_wrapping_niche_enum(rustc: str, readelf: str, tmp: pathlib.Path) -> dict[str, Any]:
    pdir = tmp / "p1"
    pdir.mkdir()

    # 1A: Runtime byte verification across all 23 inhabited values of SignedWrap
    rt_src = pdir / "wrap_rt.rs"
    rt_src.write_text(
        """#![feature(pattern_types, pattern_type_macro)]

#[allow(dead_code)]
enum SignedWrap {
    Valid(std::pat::pattern_type!(i8 is -10..=10)),
    TagA,
    TagB,
}

fn raw_byte(v: SignedWrap) -> u8 {
    unsafe { std::mem::transmute::<SignedWrap, u8>(v) }
}

fn main() {
    assert_eq!(std::mem::size_of::<SignedWrap>(), 1);
    for x in -10i8..=10i8 {
        let v: SignedWrap = SignedWrap::Valid(unsafe { std::mem::transmute(x) });
        println!("Valid({})={}", x, raw_byte(v));
    }
    println!("TagA={}", raw_byte(SignedWrap::TagA));
    println!("TagB={}", raw_byte(SignedWrap::TagB));
}
""",
        encoding="utf-8",
    )
    rt_bin = pdir / "wrap_rt"
    run([rustc, "--edition=2024", "-O", str(rt_src), "-o", str(rt_bin)])
    rt_out = run([str(rt_bin)]).stdout.strip().splitlines()
    all_runtime_bytes: dict[str, int] = {}
    for line in rt_out:
        k, v = line.split("=", 1)
        all_runtime_bytes[k] = int(v)

    # 1B: MSVC C++-like debuginfo LLVM IR for SignedWrap, SignedWrap128, and Enum17
    msvc_src = pdir / "wrap_msvc.rs"
    msvc_src.write_text(
        """#![feature(pattern_types, pattern_type_macro)]
#![crate_type = "lib"]

pub enum SignedWrap {
    Valid(std::pat::pattern_type!(i8 is -10..=10)),
    TagA,
    TagB,
}

pub enum SignedWrap128 {
    Valid(std::pat::pattern_type!(i128 is -10..=10)),
    TagA,
    TagB,
}

pub enum Enum17 {
    V0(u8), V1(u8), V2(u8), V3(u8), V4(u8), V5(u8), V6(u8), V7(u8),
    V8(u8), V9(u8), V10(u8), V11(u8), V12(u8), V13(u8), V14(u8), V15(u8),
    V16(u8),
}

#[unsafe(no_mangle)]
pub extern "C" fn touch_wrap(x: *const SignedWrap) -> usize { x as usize }

#[unsafe(no_mangle)]
pub extern "C" fn touch_wrap128(x: *const SignedWrap128) -> usize { x as usize }

#[unsafe(no_mangle)]
pub extern "C" fn touch_enum17(x: *const Enum17) -> usize { x as usize }
""",
        encoding="utf-8",
    )
    msvc_ll = pdir / "wrap_msvc.ll"
    run(
        [
            rustc,
            "--edition=2024",
            "--target",
            "x86_64-pc-windows-msvc",
            "--emit=llvm-ir",
            "-C",
            "debuginfo=2",
            "--crate-name=wrap_msvc",
            str(msvc_src),
            "-o",
            str(msvc_ll),
        ]
    )
    ll_text = msvc_ll.read_text(encoding="utf-8")

    # Parse LLVM IR metadata nodes by !N id so we can trace SignedWrap vs SignedWrap128 vs Enum17
    nodes: dict[str, str] = {}
    for line in ll_text.splitlines():
        m = re.match(r"^(!\d+)\s*=\s*(.+)$", line)
        if m:
            nodes[m.group(1)] = m.group(2)

    def collect_enum_di(enum_name_substr: str) -> dict[str, Any]:
        root_id = None
        for nid, body in nodes.items():
            if "DW_TAG_union_type" in body and enum_name_substr in body:
                root_id = nid
                break
        if root_id is None:
            return {"found": False}
        elem_m = re.search(r"elements:\s*(!\d+)", nodes[root_id])
        elem_ids = re.findall(r"!\d+", nodes[elem_m.group(1)]) if elem_m else []
        variant_fields = []
        discr_records: list[dict[str, Any]] = []
        raw_di_lines = [f"{root_id} = {nodes[root_id]}"]
        for fid in elem_ids:
            fbody = nodes.get(fid, "")
            nm_m = re.search(r'name:\s*"([^"]+)"', fbody)
            fname = nm_m.group(1) if nm_m else ""
            if fname.startswith("variant"):
                variant_fields.append(fname)
                bt_m = re.search(r"baseType:\s*(!\d+)", fbody)
                if bt_m and bt_m.group(1) in nodes:
                    wbody = nodes[bt_m.group(1)]
                    welem_m = re.search(r"elements:\s*(!\d+)", wbody)
                    welems = re.findall(r"!\d+", nodes[welem_m.group(1)]) if welem_m else []
                    rec: dict[str, Any] = {"field": fname}
                    for mid in welems:
                        mbody = nodes.get(mid, "")
                        mnm = re.search(r'name:\s*"([^"]+)"', mbody)
                        mex = re.search(r"extraData:\s*i64\s+(-?\d+)", mbody)
                        if mnm and mex:
                            key = mnm.group(1)
                            # LLVM prints extraData as signed i64; convert bit-pattern to u64
                            val_u64 = int(mex.group(1)) & ((1 << 64) - 1)
                            rec[key] = val_u64
                            if key.startswith("DISCR"):
                                raw_di_lines.append(f"{mid} = {mbody}")
                    discr_records.append(rec)
        return {
            "found": True,
            "root_node": nodes[root_id],
            "variant_fields": variant_fields,
            "discr_records": discr_records,
            "raw_di_lines": raw_di_lines,
        }

    sw_di = collect_enum_di("enum2$<wrap_msvc::SignedWrap>")
    sw128_di = collect_enum_di("enum2$<wrap_msvc::SignedWrap128>")
    e17_di = collect_enum_di("enum2$<wrap_msvc::Enum17>")

    # Extract emitted SignedWrap DISCR_BEGIN, DISCR_END, DISCR_EXACT
    emitted_begin = None
    emitted_end = None
    emitted_exacts: list[tuple[str, int]] = []
    for rec in sw_di["discr_records"]:
        if "DISCR_BEGIN" in rec and "DISCR_END" in rec:
            emitted_begin = rec["DISCR_BEGIN"]
            emitted_end = rec["DISCR_END"]
        if "DISCR_EXACT" in rec:
            emitted_exacts.append((rec["field"], rec["DISCR_EXACT"]))

    assert emitted_begin is not None and emitted_end is not None

    # Exhaustive 256-byte evaluation under:
    # (a) intrinsic.natvis DisplayString (DISCR_EXACT before in_range)
    # (b) cpp_like.rs:122-137 field-order scan (variant0 range before variant1/2 exact)
    # (c) intrinsic.natvis Expand simultaneous predicate evaluation
    # (d) corrected circular range (begin=246, end=10)
    valid_raw_set = {all_runtime_bytes[f"Valid({x})"] for x in range(-10, 11)}
    tag_a_byte = all_runtime_bytes["TagA"]
    tag_b_byte = all_runtime_bytes["TagB"]
    unused_niche_bytes = sorted(
        set(range(256)) - valid_raw_set - {tag_a_byte, tag_b_byte}
    )

    natvis_valid_matched = []
    natvis_valid_unmatched = []
    natvis_unused_false_pos = []
    expand_double_matches = []
    cpplike_order_misclassified = []

    for b in range(256):
        exact_hit = [f for f, v in emitted_exacts if v == b]
        range_hit = natvis_in_range(b, emitted_begin, emitted_end)
        if exact_hit and range_hit:
            expand_double_matches.append(b)
        # DisplayString priority: exact before range
        if exact_hit:
            disp = f"Exact({b})"
        elif range_hit:
            disp = "Valid(in_range)"
        else:
            disp = "UNMATCHED_NATVIS_FAILURE"
        # cpp_like.rs field-order scan: variant0 (range) checked before variant1/2 (exact)
        if range_hit:
            cpplike_disp = "Valid(in_range)"
        elif exact_hit:
            cpplike_disp = f"Exact({b})"
        else:
            cpplike_disp = "UNMATCHED"

        if b in valid_raw_set:
            if disp == "Valid(in_range)":
                natvis_valid_matched.append(b)
            else:
                natvis_valid_unmatched.append(b)
        elif b in (tag_a_byte, tag_b_byte):
            if cpplike_disp != f"Exact({b})":
                cpplike_order_misclassified.append({"raw_byte": b, "decoded": cpplike_disp})
        else:
            if disp == "Valid(in_range)":
                natvis_unused_false_pos.append(b)

    # Corrected decoder check across all 256 bytes
    intended_begin = all_runtime_bytes["Valid(-10)"]
    intended_end = all_runtime_bytes["Valid(10)"]
    fixed_all_valid_ok = all(natvis_in_range(b, intended_begin, intended_end) for b in valid_raw_set)
    fixed_no_exact_overlap = all(
        not natvis_in_range(b, intended_begin, intended_end) for b in (tag_a_byte, tag_b_byte)
    )
    fixed_no_unused_fp = all(
        not natvis_in_range(b, intended_begin, intended_end) for b in unused_niche_bytes
    )

    # Extract 128-bit values from SignedWrap128
    sw128_summary: dict[str, Any] = {}
    for rec in sw128_di.get("discr_records", []):
        if "DISCR128_BEGIN_HI" in rec:
            b128 = (rec["DISCR128_BEGIN_HI"] << 64) | rec["DISCR128_BEGIN_LO"]
            e128 = (rec["DISCR128_END_HI"] << 64) | rec["DISCR128_END_LO"]
            sw128_summary["emitted_begin_hex"] = hex(b128)
            sw128_summary["emitted_end_hex"] = hex(e128)
            sw128_summary["inverted_begin_le_end"] = b128 <= e128
        if "DISCR128_EXACT_HI" in rec:
            ex128 = (rec["DISCR128_EXACT_HI"] << 64) | rec["DISCR128_EXACT_LO"]
            sw128_summary.setdefault("exacts", []).append(ex128)

    # 1C: Linux native DWARF on x86_64-unknown-linux-gnu
    linux_src = pdir / "wrap_linux.rs"
    linux_src.write_text(
        """#![feature(pattern_types, pattern_type_macro)]

#[allow(dead_code)]
pub enum SignedWrap {
    Valid(std::pat::pattern_type!(i8 is -10..=10)),
    TagA,
    TagB,
}

#[unsafe(no_mangle)]
pub extern "C" fn touch_wrap_linux(x: *const SignedWrap) -> usize { x as usize }

fn main() {
    let v = SignedWrap::TagA;
    std::hint::black_box(touch_wrap_linux(&v as *const _));
}
""",
        encoding="utf-8",
    )
    linux_bin = pdir / "wrap_linux"
    run([rustc, "--edition=2024", "-C", "debuginfo=2", str(linux_src), "-o", str(linux_bin)])
    dwarf_info = run([readelf, "--debug-dump=info", str(linux_bin)]).stdout

    # Extract the SignedWrap DIE subtree from readelf --debug-dump=info
    sw_lines: list[str] = []
    lines = dwarf_info.splitlines()
    for idx, line in enumerate(lines):
        if "DW_AT_name" in line and "SignedWrap" in line:
            # Walk back 1 line to include DW_TAG_structure_type
            start = max(0, idx - 1)
            sw_lines = lines[start : min(len(lines), start + 55)]
            break
    sw_snippet = "\n".join(sw_lines)

    # Parse DW_TAG_variant entries inside SignedWrap's DW_TAG_variant_part
    variants_parsed: list[dict[str, Any]] = []
    in_vp = False
    cur_var: dict[str, Any] | None = None
    for line in sw_lines:
        if "DW_TAG_variant_part" in line:
            in_vp = True
            continue
        if not in_vp:
            continue
        if "DW_TAG_variant)" in line:
            if cur_var is not None:
                variants_parsed.append(cur_var)
            cur_var = {"has_discr_value": False, "discr_value": None, "member_name": None}
        elif cur_var is not None:
            if "DW_AT_discr_value" in line:
                m_val = re.search(r"DW_AT_discr_value\s*:\s*(\d+|0x[0-9a-fA-F]+)", line)
                cur_var["has_discr_value"] = True
                cur_var["discr_value"] = int(m_val.group(1), 0) if m_val else None
            elif "DW_AT_name" in line and cur_var["member_name"] is None:
                m_nm = re.search(r":\s*([A-Za-z0-9_]+)\s*$", line)
                if m_nm:
                    cur_var["member_name"] = m_nm.group(1)
        if "DW_TAG_structure_type" in line and variants_parsed:
            break
    if cur_var is not None:
        variants_parsed.append(cur_var)

    return {
        "actual_runtime_bytes_sample": {
            "Valid(-10)": all_runtime_bytes["Valid(-10)"],
            "Valid(-5)": all_runtime_bytes["Valid(-5)"],
            "Valid(-1)": all_runtime_bytes["Valid(-1)"],
            "Valid(0)": all_runtime_bytes["Valid(0)"],
            "Valid(10)": all_runtime_bytes["Valid(10)"],
            "TagA": tag_a_byte,
            "TagB": tag_b_byte,
        },
        "all_23_runtime_bytes": all_runtime_bytes,
        "msvc_cpp_like_emitted_discr_begin_u8": emitted_begin,
        "msvc_cpp_like_emitted_discr_end_u8": emitted_end,
        "msvc_cpp_like_emitted_discr_exacts_u8": [v for _, v in emitted_exacts],
        "intended_wrapping_begin_u8": intended_begin,
        "intended_wrapping_end_u8": intended_end,
        "exhaustive_256_byte_audit": {
            "valid_total": len(valid_raw_set),
            "natvis_display_valid_matched_count": len(natvis_valid_matched),
            "natvis_display_valid_matched_bytes": sorted(natvis_valid_matched),
            "natvis_display_valid_unmatched_count": len(natvis_valid_unmatched),
            "natvis_display_valid_unmatched_bytes": sorted(natvis_valid_unmatched),
            "unused_niche_total": len(unused_niche_bytes),
            "natvis_unused_false_positive_count": len(natvis_unused_false_pos),
            "natvis_unused_false_positive_range": [
                min(natvis_unused_false_pos),
                max(natvis_unused_false_pos),
            ]
            if natvis_unused_false_pos
            else [],
            "expand_simultaneous_exact_and_range_bytes": expand_double_matches,
            "cpplike_pseudocode_field_order_misclassified_tags": cpplike_order_misclassified,
            "corrected_circular_range_all_valid_ok": fixed_all_valid_ok,
            "corrected_circular_range_no_exact_overlap": fixed_no_exact_overlap,
            "corrected_circular_range_zero_unused_false_positives": fixed_no_unused_fp,
        },
        "msvc_signed_wrap_128": sw128_summary,
        "msvc_enum17_variant_field_count": len(e17_di.get("variant_fields", [])),
        "msvc_enum17_has_variant16": "variant16" in e17_di.get("variant_fields", []),
        "msvc_di_lines": sw_di["raw_di_lines"],
        "linux_dwarf_variants": variants_parsed,
        "linux_dwarf_untagged_valid_omits_discr_value": any(
            v["member_name"] == "Valid" and not v["has_discr_value"]
            for v in variants_parsed
        ),
        "linux_dwarf_snippet": sw_snippet,
    }


def probe_2_gdb_scripts_text_mutation(
    rustc: str, objdump: str, tmp: pathlib.Path
) -> dict[str, Any]:
    pdir = tmp / "p2"
    pdir.mkdir()
    src = pdir / "gdb_text.rs"
    src.write_text(
        """fn main() {
    let x = std::hint::black_box(42u32);
    if x == 0 {
        std::process::exit(1);
    }
}
""",
        encoding="utf-8",
    )

    configs = [
        ("debuginfo_0", ["-C", "debuginfo=0"]),
        ("debuginfo_line_directives", ["-C", "debuginfo=line-directives-only"]),
        ("debuginfo_line_tables", ["-C", "debuginfo=line-tables-only"]),
        ("debuginfo_1", ["-C", "debuginfo=1"]),
        ("debuginfo_2", ["-C", "debuginfo=2"]),
        ("debuginfo_2_strip_debuginfo", ["-C", "debuginfo=2", "-C", "strip=debuginfo"]),
        ("debuginfo_2_strip_symbols", ["-C", "debuginfo=2", "-C", "strip=symbols"]),
    ]

    results: dict[str, Any] = {}
    for label, flags in configs:
        out_bin = pdir / f"bin_{label}"
        run(
            [
                rustc,
                "--edition=2024",
                "-O",
                "--crate-name=gdb_text",
                *flags,
                str(src),
                "-o",
                str(out_bin),
            ]
        )
        secs = parse_elf64_sections(out_bin.read_bytes())
        text_bytes = secs.get(".text", b"")
        gdb_bytes = secs.get(".debug_gdb_scripts", b"")
        dis = run([objdump, "-d", "--disassemble=main", str(out_bin)], check=False).stdout
        dis_scrubbed = scrub(dis, [(str(tmp), "<TMP>")])

        # Also emit LLVM IR for main shim inspection on debuginfo_0 and debuginfo_line_directives
        volatile_load_in_ir = None
        if label in ("debuginfo_0", "debuginfo_line_directives", "debuginfo_2"):
            ll_out = pdir / f"ir_{label}.ll"
            run(
                [
                    rustc,
                    "--edition=2024",
                    "-O",
                    "--crate-name=gdb_text",
                    "--emit=llvm-ir",
                    *flags,
                    str(src),
                    "-o",
                    str(ll_out),
                ]
            )
            ll_txt = ll_out.read_text(encoding="utf-8")
            volatile_load_in_ir = (
                "load volatile i8, ptr @__rustc_debug_gdb_scripts_section__" in ll_txt
            )

        results[label] = {
            "flags": flags,
            "text_len": len(text_bytes),
            "text_sha256": sha256_bytes(text_bytes),
            "has_debug_gdb_scripts": ".debug_gdb_scripts" in secs,
            "debug_gdb_scripts_len": len(gdb_bytes),
            "debug_gdb_scripts_raw_hex": gdb_bytes.hex(),
            "main_has_movzbl": "movzbl" in dis_scrubbed,
            "volatile_load_in_llvm_ir": volatile_load_in_ir,
            "main_disasm": dis_scrubbed,
        }

    # Verify E0557 removal of #![omit_gdb_pretty_printer_section]
    omit_src = pdir / "omit_removed.rs"
    omit_src.write_text(
        """#![feature(omit_gdb_pretty_printer_section)]
#![omit_gdb_pretty_printer_section]
fn main() {}
""",
        encoding="utf-8",
    )
    omit_proc = run(
        [rustc, "--edition=2024", str(omit_src), "-o", str(pdir / "omit_bin")],
        check=False,
    )

    # Check target-spec-json emit-debug-gdb-scripts across 3 targets
    target_emit_gdb: dict[str, Any] = {}
    for tgt in (
        "x86_64-unknown-linux-gnu",
        "x86_64-pc-windows-msvc",
        "riscv64gc-unknown-none-elf",
    ):
        tp = run(
            [rustc, "-Z", "unstable-options", "--print", "target-spec-json", "--target", tgt]
        )
        tspec = json.loads(tp.stdout)
        # Note: target-spec-json omits fields equal to default (emit-debug-gdb-scripts default is true!)
        target_emit_gdb[tgt] = {
            "explicit_key_present": "emit-debug-gdb-scripts" in tspec,
            "effective_emit_debug_gdb_scripts": tspec.get("emit-debug-gdb-scripts", True),
        }

    # Check crate-type gating: rlib vs cdylib vs staticlib with -C debuginfo=2
    lib_src = pdir / "crate_types_lib.rs"
    lib_src.write_text(
        """#[unsafe(no_mangle)]
pub extern "C" fn add_one(x: u32) -> u32 { x.wrapping_add(1) }
""",
        encoding="utf-8",
    )
    crate_type_sections: dict[str, Any] = {}
    for ctype, ext in (("rlib", "rlib"), ("cdylib", "so"), ("staticlib", "a")):
        outp = pdir / f"libct.{ext}"
        run(
            [
                rustc,
                "--edition=2024",
                f"--crate-type={ctype}",
                "--crate-name=ct_probe",
                "-C",
                "debuginfo=2",
                str(lib_src),
                "-o",
                str(outp),
            ]
        )
        if ctype == "cdylib":
            secs = parse_elf64_sections(outp.read_bytes())
            crate_type_sections[ctype] = {
                "has_debug_gdb_scripts": ".debug_gdb_scripts" in secs,
                "debug_gdb_scripts_len": len(secs.get(".debug_gdb_scripts", b"")),
            }
        else:
            # Check archive members via ar
            adir = pdir / f"unpack_{ctype}"
            adir.mkdir()
            run(["ar", "x", str(outp)], cwd=adir)
            o_files = sorted(adir.glob("*.o"))
            any_gdb = False
            for of in o_files:
                b = of.read_bytes()
                if b[:4] == b"\x7fELF":
                    secs = parse_elf64_sections(b)
                    if ".debug_gdb_scripts" in secs:
                        any_gdb = True
            crate_type_sections[ctype] = {
                "o_member_count": len(o_files),
                "any_member_has_debug_gdb_scripts": any_gdb,
            }

    d0_sha = results["debuginfo_0"]["text_sha256"]
    dld_sha = results["debuginfo_line_directives"]["text_sha256"]
    return {
        "levels": results,
        "text_identical_d0_vs_line_directives": d0_sha == dld_sha,
        "text_identical_d0_vs_line_tables": d0_sha == results["debuginfo_line_tables"]["text_sha256"],
        "text_identical_d0_vs_d1": d0_sha == results["debuginfo_1"]["text_sha256"],
        "text_identical_d0_vs_d2": d0_sha == results["debuginfo_2"]["text_sha256"],
        "text_identical_d0_vs_d2_strip_debuginfo": d0_sha == results["debuginfo_2_strip_debuginfo"]["text_sha256"],
        "text_identical_line_directives_vs_d1_vs_d2": (
            dld_sha == results["debuginfo_1"]["text_sha256"] == results["debuginfo_2"]["text_sha256"]
        ),
        "text_identical_d2_vs_d2_strip_debuginfo": (
            results["debuginfo_2"]["text_sha256"] == results["debuginfo_2_strip_debuginfo"]["text_sha256"]
        ),
        "text_delta_bytes_d2_minus_d0": results["debuginfo_2"]["text_len"] - results["debuginfo_0"]["text_len"],
        "omit_gdb_pretty_printer_section_removed_rc": omit_proc.returncode,
        "omit_gdb_pretty_printer_section_stderr": scrub(omit_proc.stderr, [(str(tmp), "<TMP>")]),
        "target_spec_emit_debug_gdb_scripts": target_emit_gdb,
        "crate_type_gdb_scripts": crate_type_sections,
    }


def parse_gdb_scripts_section(raw: bytes) -> list[dict[str, Any]]:
    entries: list[dict[str, Any]] = []
    pos = 0
    while pos < len(raw):
        hdr = raw[pos]
        nul = raw.find(b"\x00", pos + 1)
        if nul == -1:
            payload = raw[pos + 1 :].decode("utf-8", errors="replace")
            entries.append({"header_byte": hdr, "payload": payload})
            break
        payload = raw[pos + 1 : nul].decode("utf-8", errors="replace")
        entries.append({"header_byte": hdr, "payload": payload})
        pos = nul + 1
    return entries


def probe_3_debugger_visualizer_transitive(rustc: str, tmp: pathlib.Path) -> dict[str, Any]:
    pdir = tmp / "p3"
    pdir.mkdir()

    shared_script = "# shared-printer-v1\n"
    leaf_script = "# leaf-printer-v1\n"

    # Diamond: vis_shared -> vis_left, vis_right -> vis_leaf
    # Also test local-vs-upstream path_erased asymmetry in vis_leaf_local_dup!
    for sub, files in [
        (
            "vis_shared",
            {
                "shared.py": shared_script,
                "lib.rs": '#![debugger_visualizer(gdb_script_file = "shared.py")]\npub fn s() -> u32 { 1 }\n',
            },
        ),
        (
            "vis_left",
            {
                "shared_copy.py": shared_script,
                "lib.rs": '#![debugger_visualizer(gdb_script_file = "shared_copy.py")]\npub fn l() -> u32 { vis_shared::s() + 2 }\n',
            },
        ),
        (
            "vis_right",
            {
                "lib.rs": "pub fn r() -> u32 { vis_shared::s() + 3 }\n",
            },
        ),
        (
            "vis_leaf",
            {
                "leaf.py": leaf_script,
                "main.rs": '#![debugger_visualizer(gdb_script_file = "leaf.py")]\nfn main() { std::hint::black_box(vis_left::l() + vis_right::r()); }\n',
            },
        ),
        (
            "vis_leaf_local_dup",
            {
                "local_shared.py": shared_script,
                "main.rs": '#![debugger_visualizer(gdb_script_file = "local_shared.py")]\nfn main() { std::hint::black_box(vis_shared::s()); }\n',
            },
        ),
    ]:
        d = pdir / sub
        d.mkdir()
        for fn, txt in files.items():
            (d / fn).write_text(txt, encoding="utf-8")

    out = pdir / "out"
    out.mkdir()

    # Build rlibs
    run(
        [
            rustc, "--edition=2024", "--crate-type=rlib", "--crate-name=vis_shared",
            "-C", "debuginfo=2", str(pdir / "vis_shared/lib.rs"),
            "-o", str(out / "libvis_shared.rlib"),
        ]
    )
    run(
        [
            rustc, "--edition=2024", "--crate-type=rlib", "--crate-name=vis_left",
            "-C", "debuginfo=2",
            "--extern", f"vis_shared={out / 'libvis_shared.rlib'}",
            "-L", f"dependency={out}",
            str(pdir / "vis_left/lib.rs"),
            "-o", str(out / "libvis_left.rlib"),
        ]
    )
    run(
        [
            rustc, "--edition=2024", "--crate-type=rlib", "--crate-name=vis_right",
            "-C", "debuginfo=2",
            "--extern", f"vis_shared={out / 'libvis_shared.rlib'}",
            "-L", f"dependency={out}",
            str(pdir / "vis_right/lib.rs"),
            "-o", str(out / "libvis_right.rlib"),
        ]
    )

    # Check none of the rlib .o members contain .debug_gdb_scripts
    rlib_gdb_scripts_present = False
    for rlib in (out / "libvis_shared.rlib", out / "libvis_left.rlib", out / "libvis_right.rlib"):
        udir = pdir / f"unpack_{rlib.stem}"
        udir.mkdir()
        run(["ar", "x", str(rlib)], cwd=udir)
        for of in udir.glob("*.o"):
            b = of.read_bytes()
            if b[:4] == b"\x7fELF" and ".debug_gdb_scripts" in parse_elf64_sections(b):
                rlib_gdb_scripts_present = True

    # Build vis_leaf
    leaf_bin = out / "vis_leaf"
    run(
        [
            rustc, "--edition=2024", "--crate-name=vis_leaf",
            "-C", "debuginfo=2",
            "--extern", f"vis_left={out / 'libvis_left.rlib'}",
            "--extern", f"vis_right={out / 'libvis_right.rlib'}",
            "-L", f"dependency={out}",
            str(pdir / "vis_leaf/main.rs"),
            "-o", str(leaf_bin),
        ]
    )
    leaf_raw = parse_elf64_sections(leaf_bin.read_bytes()).get(".debug_gdb_scripts", b"")
    leaf_entries = parse_gdb_scripts_section(leaf_raw)
    shared_count = sum(1 for e in leaf_entries if shared_script in e["payload"])

    # Build vis_leaf_local_dup (tests local Some(path) vs upstream None in BTreeSet!)
    dup_bin = out / "vis_leaf_local_dup"
    run(
        [
            rustc, "--edition=2024", "--crate-name=vis_leaf_local_dup",
            "-C", "debuginfo=2",
            "--extern", f"vis_shared={out / 'libvis_shared.rlib'}",
            "-L", f"dependency={out}",
            str(pdir / "vis_leaf_local_dup/main.rs"),
            "-o", str(dup_bin),
        ]
    )
    dup_raw = parse_elf64_sections(dup_bin.read_bytes()).get(".debug_gdb_scripts", b"")
    dup_entries = parse_gdb_scripts_section(dup_raw)
    dup_shared_count = sum(1 for e in dup_entries if shared_script in e["payload"])

    return {
        "rlib_emits_debug_gdb_scripts": rlib_gdb_scripts_present,
        "diamond_leaf": {
            "bin_debug_gdb_scripts_bytes": len(leaf_raw),
            "entry_count": len(leaf_entries),
            "entries": leaf_entries,
            "deduplicated_shared_script_count": shared_count,
        },
        "local_vs_upstream_path_erased_asymmetry": {
            "bin_debug_gdb_scripts_bytes": len(dup_raw),
            "entry_count": len(dup_entries),
            "entries": dup_entries,
            "shared_script_occurrences": dup_shared_count,
            "local_and_upstream_identical_bytes_duplicated": dup_shared_count == 2,
        },
    }


def probe_4_split_debuginfo_and_thorin_dwp(rustc: str, tmp: pathlib.Path) -> dict[str, Any]:
    pdir = tmp / "p4"
    pdir.mkdir()

    dep_code = "pub fn compute_dep(x: u64) -> u64 { x.wrapping_mul(3).wrapping_add(7) }\n"
    app_code = "fn main() { std::hint::black_box(dep_krate::compute_dep(19)); }\n"

    matrix_specs = [
        ("dwarf4_off_single", 4, "off", "single"),
        ("dwarf4_unpacked_split", 4, "unpacked", "split"),
        ("dwarf4_unpacked_single", 4, "unpacked", "single"),
        ("dwarf4_packed_split", 4, "packed", "split"),
        ("dwarf4_packed_single", 4, "packed", "single"),
        ("dwarf5_off_single", 5, "off", "single"),
        ("dwarf5_unpacked_split", 5, "unpacked", "split"),
        ("dwarf5_unpacked_single", 5, "unpacked", "single"),
        ("dwarf5_packed_split", 5, "packed", "split"),
        ("dwarf5_packed_single", 5, "packed", "single"),
    ]

    matrix: dict[str, Any] = {}
    for key, dwarf_ver, split_mode, split_kind in matrix_specs:
        cdir = pdir / key
        cdir.mkdir()
        (cdir / "dep.rs").write_text(dep_code, encoding="utf-8")
        (cdir / "app.rs").write_text(app_code, encoding="utf-8")
        common = [
            "--edition=2024",
            "-C", "debuginfo=2",
            "-C", "codegen-units=1",
            "-Z", f"dwarf-version={dwarf_ver}",
            "-C", f"split-debuginfo={split_mode}",
        ]
        if split_mode != "off":
            common += ["-Z", f"split-dwarf-kind={split_kind}"]

        rlib = cdir / "libdep_krate.rlib"
        run(
            [
                rustc, *common,
                "--crate-type=rlib", "--crate-name=dep_krate",
                str(cdir / "dep.rs"), "-o", str(rlib),
            ],
            cwd=cdir,
        )
        exe = cdir / "app"
        run(
            [
                rustc, *common,
                "--crate-name=app",
                "--extern", f"dep_krate={rlib}",
                "-L", f"dependency={cdir}",
                str(cdir / "app.rs"), "-o", str(exe),
            ],
            cwd=cdir,
        )

        # Count .dwo members inside rlib
        ar_members = run(["ar", "t", str(rlib)]).stdout.splitlines()
        dwo_in_rlib = sum(1 for m in ar_members if m.endswith(".dwo"))
        loose_dwos = sorted(p.name for p in cdir.glob("*.dwo"))
        dwp = cdir / "app.dwp"
        has_dwp = dwp.exists()
        dwp_size = dwp.stat().st_size if has_dwp else 0
        dwp_sections: list[str] = []
        cu_index_hdr: dict[str, int] = {}
        if has_dwp:
            secs = parse_elf64_sections(dwp.read_bytes())
            dwp_sections = [s for s in secs.keys() if s.startswith(".debug_")]
            if ".debug_cu_index" in secs:
                cu_index_hdr = parse_cu_index_unit_count(secs[".debug_cu_index"])

        matrix[key] = {
            "dwarf_version": dwarf_ver,
            "split_debuginfo": split_mode,
            "split_dwarf_kind": split_kind,
            "exe_size": exe.stat().st_size,
            "dwo_members_in_rlib": dwo_in_rlib,
            "loose_dwo_files": len(loose_dwos),
            "has_dwp": has_dwp,
            "dwp_size": dwp_size,
            "dwp_sections": dwp_sections,
            "cu_index_header": cu_index_hdr,
            "cu_index_unit_count": cu_index_hdr.get("unit_count", 0),
        }

    # Reproducibility across two distinct directories with different path lengths
    def build_remapped(dirname: str, use_remap_cwd: bool) -> tuple[str, str, int, int]:
        rdir = pdir / dirname
        rdir.mkdir()
        (rdir / "dep.rs").write_text(dep_code, encoding="utf-8")
        (rdir / "app.rs").write_text(app_code, encoding="utf-8")
        flags = [
            "--edition=2024",
            "-C", "debuginfo=2",
            "-C", "codegen-units=1",
            "-Z", "dwarf-version=5",
            "-C", "split-debuginfo=packed",
            "-Z", "split-dwarf-kind=split",
            f"--remap-path-prefix={rdir}=/remap",
        ]
        if use_remap_cwd:
            flags += ["-Z", "remap-cwd-prefix=/remap"]
        rlib = rdir / "libdep_krate.rlib"
        run(
            [
                rustc, *flags,
                "--crate-type=rlib", "--crate-name=dep_krate",
                str(rdir / "dep.rs"), "-o", str(rlib),
            ],
            cwd=rdir,
        )
        exe = rdir / "app"
        run(
            [
                rustc, *flags,
                "--crate-name=app",
                "--extern", f"dep_krate={rlib}",
                "-L", f"dependency={rdir}",
                str(rdir / "app.rs"), "-o", str(exe),
            ],
            cwd=rdir,
        )
        dwp = rdir / "app.dwp"
        return (
            sha256_file(dwp),
            sha256_file(exe),
            dwp.stat().st_size,
            exe.stat().st_size,
        )

    dwp_a1, exe_a1, dwp_sz_a1, exe_sz_a1 = build_remapped("repro_alpha", False)
    dwp_b1, exe_b1, dwp_sz_b1, exe_sz_b1 = build_remapped("repro_beta_distinct_longer_dir", False)

    dwp_a2, exe_a2, dwp_sz_a2, exe_sz_a2 = build_remapped("repro_cwd_alpha", True)
    dwp_b2, exe_b2, dwp_sz_b2, exe_sz_b2 = build_remapped("repro_cwd_beta_distinct_longer_dir", True)

    return {
        "matrix": matrix,
        "remap_path_prefix_only": {
            "remapped_packed_dwp_bit_identical": dwp_a1 == dwp_b1,
            "remapped_packed_exe_bit_identical": exe_a1 == exe_b1,
            "dwp_sha256_pair": [dwp_a1, dwp_b1],
            "exe_sha256_pair": [exe_a1, exe_b1],
            "dwp_size_pair": [dwp_sz_a1, dwp_sz_b1],
            "exe_size_pair": [exe_sz_a1, exe_sz_b1],
        },
        "remap_path_and_cwd_prefix": {
            "remapped_packed_dwp_bit_identical": dwp_a2 == dwp_b2,
            "remapped_packed_exe_bit_identical": exe_a2 == exe_b2,
            "dwp_sha256_pair": [dwp_a2, dwp_b2],
            "exe_sha256_pair": [exe_a2, exe_b2],
            "dwp_size_pair": [dwp_sz_a2, dwp_sz_b2],
            "exe_size_pair": [exe_sz_a2, exe_sz_b2],
        },
    }


def probe_5_coroutine_and_collapse_debuginfo(
    rustc: str, readelf: str, tmp: pathlib.Path
) -> dict[str, Any]:
    pdir = tmp / "p5"
    pdir.mkdir()

    # 5A: Coroutine __state DWARF encoding on Linux vs MSVC VariantNames (1-yield -> states 0..3)
    coro_src = pdir / "coro.rs"
    coro_src.write_text(
        """#![feature(coroutines, coroutine_trait)]
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

fn make_coro(seed: u32) -> impl Coroutine<Yield = u32, Return = u32> {
    #[coroutine]
    move || {
        let a = seed + 1;
        yield a;
        a + 2
    }
}

fn main() {
    let mut c = Box::pin(make_coro(10));
    let r1 = Pin::as_mut(&mut c).resume(());
    let r2 = Pin::as_mut(&mut c).resume(());
    if let (CoroutineState::Yielded(x), CoroutineState::Complete(y)) = (r1, r2) {
        std::hint::black_box(x + y);
    }
}
""",
        encoding="utf-8",
    )
    coro_bin = pdir / "coro_linux"
    run([rustc, "--edition=2024", "-C", "debuginfo=2", str(coro_src), "-o", str(coro_bin)])
    coro_dwarf = run([readelf, "--debug-dump=info", str(coro_bin)]).stdout

    has_dunder_state = False
    dunder_state_artificial = False
    numeric_variant_names: list[str] = []
    lines = coro_dwarf.splitlines()
    for i, line in enumerate(lines):
        if "DW_AT_name" in line and "__state" in line:
            has_dunder_state = True
            # Check subsequent attributes of this DIE and sibling DW_TAG_variant DIEs
            window = lines[i : min(len(lines), i + 120)]
            for w in window[:12]:
                if "DW_AT_artificial" in w:
                    dunder_state_artificial = True
            # Collect variant member names inside this DW_TAG_variant_part
            in_var = False
            for w in window:
                if "DW_TAG_variant)" in w:
                    in_var = True
                elif in_var and "DW_AT_name" in w:
                    m = re.search(r":\s*([0-9]+)\s*$", w)
                    if m:
                        numeric_variant_names.append(m.group(1))
                    in_var = False
                elif "DW_TAG_structure_type" in w and numeric_variant_names:
                    break
            break

    # Also compile coroutine for x86_64-pc-windows-msvc --emit=llvm-ir to check VariantNames
    coro_lib_src = pdir / "coro_msvc.rs"
    coro_lib_src.write_text(
        """#![feature(coroutines, coroutine_trait)]
#![crate_type = "lib"]
use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[unsafe(no_mangle)]
pub fn run_coro(seed: u32) -> u32 {
    let mut c = Box::pin(#[coroutine] move || {
        let a = seed + 1;
        yield a;
        a + 2
    });
    match Pin::as_mut(&mut c).resume(()) {
        CoroutineState::Yielded(v) => v,
        CoroutineState::Complete(v) => v,
    }
}
""",
        encoding="utf-8",
    )
    coro_msvc_ll = pdir / "coro_msvc.ll"
    run(
        [
            rustc, "--edition=2024",
            "--target", "x86_64-pc-windows-msvc",
            "--emit=llvm-ir", "-C", "debuginfo=2",
            str(coro_lib_src), "-o", str(coro_msvc_ll),
        ]
    )
    coro_msvc_txt = coro_msvc_ll.read_text(encoding="utf-8")
    msvc_coro_enumerators = sorted(
        set(
            re.findall(
                r'!DIEnumerator\(name:\s*"(Unresumed|Returned|Panicked|Suspend\d+)",\s*value:\s*(\d+)[^)]*\)',
                coro_msvc_txt,
            )
        ),
        key=lambda kv: int(kv[1]),
    )

    # 5B: #[collapse_debuginfo(yes|no|external)] + -C collapse-macro-debuginfo override matrix
    mac_up_src = pdir / "mac_up.rs"
    mac_up_src.write_text(
        """#[macro_export]
macro_rules! m_default {
    ($x:expr) => {{
        let v_def = $x + 11;
        std::hint::black_box(v_def)
    }};
}

#[macro_export]
#[collapse_debuginfo(yes)]
macro_rules! m_yes {
    ($x:expr) => {{
        let v_yes = $x + 22;
        std::hint::black_box(v_yes)
    }};
}

#[macro_export]
#[collapse_debuginfo(no)]
macro_rules! m_no {
    ($x:expr) => {{
        let v_no = $x + 33;
        std::hint::black_box(v_no)
    }};
}

#[macro_export]
#[collapse_debuginfo(external)]
macro_rules! m_ext {
    ($x:expr) => {{
        let v_ext = $x + 44;
        std::hint::black_box(v_ext)
    }};
}
""",
        encoding="utf-8",
    )
    mac_up_rlib = pdir / "libmac_up.rlib"
    run(
        [
            rustc, "--edition=2024", "--crate-type=rlib", "--crate-name=mac_up",
            "-C", "debuginfo=2", str(mac_up_src), "-o", str(mac_up_rlib),
        ]
    )

    # Build 4 single-macro downstream binaries (and 2 CLI-override binaries) to isolate each macro cleanly!
    collapse_matrix: dict[str, Any] = {}
    for case_name, macro_call, extra_flags in [
        ("attr_default_cli_default", "mac_up::m_default!(x)", []),
        ("attr_yes_cli_default", "mac_up::m_yes!(x)", []),
        ("attr_no_cli_default", "mac_up::m_no!(x)", []),
        ("attr_external_cli_default", "mac_up::m_ext!(x)", []),
        ("attr_no_cli_yes_override", "mac_up::m_no!(x)", ["-C", "collapse-macro-debuginfo=yes"]),
        ("attr_yes_cli_no_override", "mac_up::m_yes!(x)", ["-C", "collapse-macro-debuginfo=no"]),
    ]:
        dn_src = pdir / f"dn_{case_name}.rs"
        dn_src.write_text(
            f"""#[inline(never)]
pub fn invoke_target(x: u64) -> u64 {{
    {macro_call}
}}

fn main() {{
    std::hint::black_box(invoke_target(5));
}}
""",
            encoding="utf-8",
        )
        dn_bin = pdir / f"dn_{case_name}"
        run(
            [
                rustc, "--edition=2024", "-C", "debuginfo=2",
                "--extern", f"mac_up={mac_up_rlib}",
                "-L", f"dependency={pdir}",
                *extra_flags,
                str(dn_src), "-o", str(dn_bin),
            ]
        )
        dline = run([readelf, "--debug-dump=decodedline", str(dn_bin)]).stdout
        dinfo = run([readelf, "--debug-dump=info", str(dn_bin)]).stdout
        # Check whether mac_up.rs appears in decodedline and what DW_AT_decl_line v_* local gets
        refs_mac_up = "mac_up.rs" in dline
        var_decl_lines: dict[str, int] = {}
        di_lines = dinfo.splitlines()
        for idx, dl in enumerate(di_lines):
            m_var = re.search(r"DW_AT_name\s*:.*\b(v_(?:def|yes|no|ext))\b", dl)
            if m_var:
                vname = m_var.group(1)
                for fwd in di_lines[idx : min(len(di_lines), idx + 8)]:
                    m_ln = re.search(r"DW_AT_decl_line\s*:\s*(\d+)", fwd)
                    if m_ln:
                        var_decl_lines[vname] = int(m_ln.group(1))
                        break
        collapse_matrix[case_name] = {
            "macro_call": macro_call,
            "extra_flags": extra_flags,
            "decodedline_references_mac_up_rs": refs_mac_up,
            "local_var_decl_lines": var_decl_lines,
        }

    # Also test local (same-crate) m_yes vs m_ext vs m_no vs m_default
    local_mac_src = pdir / "mac_local.rs"
    local_mac_src.write_text(
        """macro_rules! loc_default { ($x:expr) => {{ let v_def = $x + 1; std::hint::black_box(v_def) }}; }
#[collapse_debuginfo(yes)]
macro_rules! loc_yes { ($x:expr) => {{ let v_yes = $x + 2; std::hint::black_box(v_yes) }}; }
#[collapse_debuginfo(no)]
macro_rules! loc_no { ($x:expr) => {{ let v_no = $x + 3; std::hint::black_box(v_no) }}; }
#[collapse_debuginfo(external)]
macro_rules! loc_ext { ($x:expr) => {{ let v_ext = $x + 4; std::hint::black_box(v_ext) }}; }

fn main() {
    let x = std::hint::black_box(10u64);
    let _ = loc_default!(x);
    let _ = loc_yes!(x);
    let _ = loc_no!(x);
    let _ = loc_ext!(x);
}
""",
        encoding="utf-8",
    )
    local_mac_bin = pdir / "mac_local"
    run([rustc, "--edition=2024", "-C", "debuginfo=2", str(local_mac_src), "-o", str(local_mac_bin)])
    local_dinfo = run([readelf, "--debug-dump=info", str(local_mac_bin)]).stdout
    local_var_lines: dict[str, int] = {}
    ldi = local_dinfo.splitlines()
    for idx, dl in enumerate(ldi):
        m_var = re.search(r"DW_AT_name\s*:.*\b(v_(?:def|yes|no|ext))\b", dl)
        if m_var:
            vname = m_var.group(1)
            for fwd in ldi[idx : min(len(ldi), idx + 8)]:
                m_ln = re.search(r"DW_AT_decl_line\s*:\s*(\d+)", fwd)
                if m_ln:
                    local_var_lines[vname] = int(m_ln.group(1))
                    break

    return {
        "coroutine_linux_dwarf": {
            "has_dunder_state_discr": has_dunder_state,
            "dunder_state_is_artificial": dunder_state_artificial,
            "numeric_variant_names": numeric_variant_names,
        },
        "coroutine_msvc_cpp_like": {
            "variant_names_enumerators": [
                {"name": n, "value": int(v)} for n, v in msvc_coro_enumerators
            ],
        },
        "collapse_debuginfo_cross_crate_matrix": collapse_matrix,
        "collapse_debuginfo_same_crate_decl_lines": {
            "macro_def_lines": {"loc_default": 1, "loc_yes": 3, "loc_no": 5, "loc_ext": 7},
            "call_site_lines": {"loc_default": 11, "loc_yes": 12, "loc_no": 13, "loc_ext": 14},
            "observed_dw_at_decl_lines": local_var_lines,
        },
    }


def main() -> int:
    rustc = find_rustc()
    readelf = find_tool("readelf", rustc)
    objdump = find_tool("objdump", rustc)
    rustc_ver = run([rustc, "--version", "--verbose"]).stdout.strip()

    with tempfile.TemporaryDirectory(prefix="probe_dwarf_dwp_") as tmp_str:
        tmp = pathlib.Path(tmp_str)
        report = {
            "rustc_version_verbose": rustc_ver,
            "probe_1_wrapping_niche_enum_discr_inversion": probe_1_wrapping_niche_enum(
                rustc, readelf, tmp
            ),
            "probe_2_gdb_scripts_text_mutation": probe_2_gdb_scripts_text_mutation(
                rustc, objdump, tmp
            ),
            "probe_3_debugger_visualizer_transitive": probe_3_debugger_visualizer_transitive(
                rustc, tmp
            ),
            "probe_4_split_debuginfo_and_thorin_dwp": probe_4_split_debuginfo_and_thorin_dwp(
                rustc, tmp
            ),
            "probe_5_coroutine_and_collapse_debuginfo": probe_5_coroutine_and_collapse_debuginfo(
                rustc, readelf, tmp
            ),
        }

    out_path = pathlib.Path(sys.argv[1]) if len(sys.argv) > 1 else None
    rendered = json.dumps(report, indent=2) + "\n"
    if out_path:
        out_path.parent.mkdir(parents=True, exist_ok=True)
        out_path.write_text(rendered, encoding="utf-8")
        print(f"Wrote {out_path} ({len(rendered)} bytes)")
    else:
        print(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
