#!/usr/bin/env python3
import glob
import json
import os
import re
import shutil
import subprocess
import tempfile
from collections import Counter, defaultdict
from pathlib import Path

RUN_DIR = Path(os.environ.get("WORK_DIR", "/tmp/reloc_probe"))
TMP_DIR = RUN_DIR / "tmp"
TMP_DIR.mkdir(parents=True, exist_ok=True)

TC_ROOT = Path(os.path.expanduser("~/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu"))
RUSTC = TC_ROOT / "bin" / "rustc"
LLVM_BIN = TC_ROOT / "lib" / "rustlib" / "x86_64-unknown-linux-gnu" / "bin"
LLVM_AR = LLVM_BIN / "llvm-ar"
LLVM_READOBJ = LLVM_BIN / "llvm-readobj"
LLVM_OBJDUMP = LLVM_BIN / "llvm-objdump"
LLC = LLVM_BIN / "llc"

S1991 = Path(os.environ.get("WORK_DIR", "/tmp/reloc_probe"))

TIER1_TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
]

CRATE_PREFIXES = ["libcore-", "liballoc-", "libstd-", "libcompiler_builtins-"]

RELOC_LINE_RE = re.compile(r"\b(R_[A-Za-z0-9_]+|IMAGE_REL_[A-Za-z0-9_]+|ARM64_RELOC_[A-Za-z0-9_]+|X86_64_RELOC_[A-Za-z0-9_]+|GENERIC_RELOC_[A-Za-z0-9_]+)\b")
FORMAT_RE = re.compile(r"Format:\s*(.+)")

def parse_relocs_and_format(readobj_output: str):
    fmt = None
    relocs = Counter()
    for line in readobj_output.splitlines():
        if fmt is None:
            m_fmt = FORMAT_RE.search(line)
            if m_fmt:
                fmt = m_fmt.group(1).strip()
        m_rel = RELOC_LINE_RE.search(line)
        if m_rel:
            rtype = m_rel.group(1)
            if rtype.startswith(("R_", "IMAGE_REL_", "ARM64_RELOC_", "X86_64_RELOC_", "GENERIC_RELOC_")):
                relocs[rtype] += 1
    return fmt, relocs

def measure_rlibs():
    results = {}
    for target in TIER1_TARGETS:
        tdir = TC_ROOT / "lib" / "rustlib" / target / "lib"
        target_relocs = Counter()
        per_crate = {}
        obj_format = None
        total_objs = 0
        for prefix in CRATE_PREFIXES:
            matches = sorted(tdir.glob(f"{prefix}*.rlib"))
            if not matches:
                continue
            rlib = matches[0]
            crate_name = prefix.rstrip("-")
            with tempfile.TemporaryDirectory(dir=TMP_DIR) as work:
                subprocess.run([str(LLVM_AR), "x", str(rlib)], cwd=work, check=True)
                objs = sorted([str(p) for p in Path(work).glob("*.o") if not p.name.endswith(".rmeta")])
                total_objs += len(objs)
                if not objs:
                    continue
                proc = subprocess.run(
                    [str(LLVM_READOBJ), "--relocations"] + objs,
                    cwd=work, text=True, capture_output=True, check=True
                )
                fmt, c_relocs = parse_relocs_and_format(proc.stdout)
                if fmt and not obj_format:
                    obj_format = fmt
                target_relocs.update(c_relocs)
                per_crate[crate_name] = {
                    "rlib_filename": rlib.name,
                    "object_count": len(objs),
                    "total_relocations": sum(c_relocs.values()),
                    "distinct_relocation_kinds": len(c_relocs),
                    "relocation_counts": dict(c_relocs.most_common()),
                }
        results[target] = {
            "object_format": obj_format,
            "total_objects_scanned": total_objs,
            "total_relocations": sum(target_relocs.values()),
            "distinct_relocation_kinds": len(target_relocs),
            "relocation_counts": dict(target_relocs.most_common()),
            "per_crate": per_crate,
        }
        print(f"[rlib] {target}: format={obj_format}, objs={total_objs}, total_relocs={sum(target_relocs.values())}, kinds={len(target_relocs)}")
    return results

PROBE_RS = """#![no_std]
#![crate_type = "rlib"]

pub static GLOBAL_COUNTER: core::sync::atomic::AtomicUsize = core::sync::atomic::AtomicUsize::new(42);
pub static mut STATIC_TABLE: [u64; 4] = [1, 2, 3, 4];

#[inline(never)]
pub fn external_helper(x: u64) -> u64 {
    x.wrapping_mul(0x9E3779B97F4A7C15).rotate_left(17)
}

pub trait Processor {
    fn process(&self, val: u64) -> u64;
}

pub struct Multiplier(pub u64);
impl Processor for Multiplier {
    fn process(&self, val: u64) -> u64 {
        external_helper(val.wrapping_add(self.0))
    }
}

#[no_mangle]
pub extern "C" fn probe_entry(p: &dyn Processor, idx: usize) -> u64 {
    let base = GLOBAL_COUNTER.fetch_add(1, core::sync::atomic::Ordering::SeqCst) as u64;
    let tbl = unsafe { STATIC_TABLE[idx & 3] };
    let fn_ptr: fn(u64) -> u64 = external_helper;
    p.process(base ^ tbl) ^ fn_ptr(idx as u64)
}
"""

def measure_probes():
    probe_src = TMP_DIR / "probe_reloc.rs"
    probe_src.write_text(PROBE_RS, encoding="utf-8")
    probe_results = {}
    for target in TIER1_TARGETS:
        probe_results[target] = {}
        for opt in ["0", "3", "s"]:
            obj_out = TMP_DIR / f"probe_{target}_O{opt}.o"
            subprocess.run(
                [str(RUSTC), "--target", target, f"-Copt-level={opt}", "--emit=obj", str(probe_src), "-o", str(obj_out)],
                check=True
            )
            proc = subprocess.run(
                [str(LLVM_READOBJ), "--relocations", "--sections", str(obj_out)],
                text=True, capture_output=True, check=True
            )
            fmt, relocs = parse_relocs_and_format(proc.stdout)
            sec_names = re.findall(r"Name:\s*(\.[A-Za-z0-9_$.]+|__[A-Za-z0-9_]+)\b", proc.stdout)
            probe_results[target][f"probe-O{opt}"] = {
                "object_format": fmt,
                "object_size_bytes": obj_out.stat().st_size,
                "section_count": len(sec_names),
                "sections_sample": sec_names[:15],
                "total_relocations": sum(relocs.values()),
                "distinct_relocation_kinds": len(relocs),
                "relocation_counts": dict(relocs.most_common()),
            }
    return probe_results

def extract_rust_target_features():
    tf_path = S1991 / "compiler" / "rustc_target" / "src" / "target_features.rs"
    txt = tf_path.read_text(encoding="utf-8")
    def parse_block(start_marker, end_marker):
        s = txt.find(start_marker)
        e = txt.find(end_marker, s)
        block = txt[s:e]
        feats = []
        for m in re.finditer(r'\("([^"]+)",\s*(Stable|Unstable\([^)]+\)|Forbidden\([^)]+\)),\s*&\[([^\]]*)\]\)', block):
            name, stab, deps = m.group(1), m.group(2), m.group(3)
            dep_list = [d.strip().strip('"') for d in deps.split(",") if d.strip()]
            feats.append({"feature": name, "stability": stab, "implies": dep_list})
        return feats
    x86_feats = parse_block("const X86_FEATURES:", "const HEXAGON_FEATURES:")
    aarch64_feats = parse_block("const AARCH64_FEATURES:", "const AARCH64_TIED_FEATURES:")
    return {
        "x86_total": len(x86_feats),
        "x86_stable": sum(1 for f in x86_feats if f["stability"] == "Stable"),
        "x86_unstable": sum(1 for f in x86_feats if f["stability"].startswith("Unstable")),
        "x86_forbidden": sum(1 for f in x86_feats if f["stability"].startswith("Forbidden")),
        "x86_features": x86_feats,
        "aarch64_total": len(aarch64_feats),
        "aarch64_stable": sum(1 for f in aarch64_feats if f["stability"] == "Stable"),
        "aarch64_unstable": sum(1 for f in aarch64_feats if f["stability"].startswith("Unstable")),
        "aarch64_forbidden": sum(1 for f in aarch64_feats if f["stability"].startswith("Forbidden")),
        "aarch64_features": aarch64_feats,
    }

def measure_disassembly_mnemonics():
    mnemonic_stats = {}
    for target in ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu", "aarch64-unknown-linux-gnu"]:
        tdir = TC_ROOT / "lib" / "rustlib" / target / "lib"
        rlib = sorted(tdir.glob("libcore-*.rlib"))[0]
        with tempfile.TemporaryDirectory(dir=TMP_DIR) as work:
            subprocess.run([str(LLVM_AR), "x", str(rlib)], cwd=work, check=True)
            objs = sorted([str(p) for p in Path(work).glob("*.o") if not p.name.endswith(".rmeta")])
            proc = subprocess.run(
                [str(LLVM_OBJDUMP), "-d", "--no-show-raw-insn"] + objs,
                cwd=work, text=True, capture_output=True, check=True
            )
            mnems = Counter()
            for line in proc.stdout.splitlines():
                m = re.match(r"^\s*[0-9a-fA-F]+:\s+([a-zA-Z0-9_.]+)", line)
                if m:
                    op = m.group(1).lower()
                    if op in ("lock", "rep", "repz", "repne", "repnz", "data16", "cs", "ds", "es", "fs", "gs", "ss", "rex64"):
                        rest = line.split(None, 2)
                        if len(rest) >= 3:
                            sub = rest[2].split()[0].lower()
                            op = f"{op} {sub}"
                    mnems[op] += 1
            mnemonic_stats[target] = {
                "rlib": rlib.name,
                "total_instructions": sum(mnems.values()),
                "distinct_mnemonics": len(mnems),
                "top_50_mnemonics": dict(mnems.most_common(50)),
                "all_mnemonics": dict(mnems.most_common()),
            }
            print(f"[disasm] {target}: total_insns={sum(mnems.values())}, distinct_mnemonics={len(mnems)}")
    return mnemonic_stats

if __name__ == "__main__":
    rlibs = measure_rlibs()
    probes = measure_probes()
    tfeats = extract_rust_target_features()
    disasm = measure_disassembly_mnemonics()
    out = {
        "tier1_rlib_relocations": rlibs,
        "tier1_probe_relocations": probes,
        "rust_1991_target_features": tfeats,
        "libcore_disassembly_mnemonics": disasm,
    }
    (RUN_DIR / "measured_relocs_and_isa.json").write_text(json.dumps(out, indent=2), encoding="utf-8")
    print("Wrote measured_relocs_and_isa.json successfully.")
