#!/usr/bin/env python3
import glob, json, os, re, shutil, subprocess, tarfile
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path

SYSROOT = Path("/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu")
BIN_DIR = SYSROOT / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
LLVM_AR = str(BIN_DIR / "llvm-ar")
LLVM_READOBJ = str(BIN_DIR / "llvm-readobj")
LLVM_OBJDUMP = str(BIN_DIR / "llvm-objdump")
RUSTC = "rustc"
OUT_DIR = Path(".")

TARGETS = [
    "x86_64-unknown-linux-gnu",
    "i686-unknown-linux-gnu",
    "aarch64-unknown-linux-gnu",
    "aarch64-apple-darwin",
    "x86_64-pc-windows-msvc",
    "x86_64-pc-windows-gnu",
    "i686-pc-windows-msvc",
    "aarch64-pc-windows-msvc",
]

SAMPLE_CRATES = [
    ("hashbrown-0.16.1.crate", "src/lib.rs", "2021", []),
    ("itoa-1.0.15.crate", "src/lib.rs", "2018", []),
    ("ryu-1.0.20.crate", "src/lib.rs", "2018", []),
    ("bitflags-2.10.0.crate", "src/lib.rs", "2021", []),
    ("byteorder-1.5.0.crate", "src/lib.rs", "2021", ["--cfg", 'feature="std"']),
    ("bytes-1.11.0.crate", "src/lib.rs", "2021", ["--cfg", 'feature="std"']),
    ("once_cell-1.21.3.crate", "src/lib.rs", "2021", ["--cfg", 'feature="std"', "--cfg", 'feature="alloc"']),
    ("memchr-2.7.6.crate", "src/lib.rs", "2021", ["--cfg", 'feature="std"', "--cfg", 'feature="alloc"']),
    ("regex-syntax-0.8.8.crate", "src/lib.rs", "2021", ["--cfg", 'feature="std"', "--cfg", 'feature="unicode"']),
    ("unicode-ident-1.0.22.crate", "src/lib.rs", "2018", []),
]

def normalize_sec(name: str, target: str) -> str:
    if "linux" in target:
        for p in [".text.unlikely.", ".text.hot.", ".text.startup.", ".text.exit.", ".text.", ".rodata.cst4.", ".rodata.cst8.", ".rodata.cst16.", ".rodata.cst32.", ".rodata.str1.", ".rodata.", ".data.rel.ro.local.", ".data.rel.ro.", ".data.", ".bss.", ".tbss.", ".tdata.", ".rela.text.", ".rela.rodata.", ".rela.data.rel.ro.", ".rela.data.", ".rela.init_array.", ".rela.gcc_except_table.", ".rel.text.", ".rel.rodata.", ".rel.data.rel.ro.", ".rel.data.", ".rel.init_array.", ".rel.gcc_except_table.", ".gcc_except_table."]:
            if name.startswith(p):
                return p + "<sym>"
    elif "windows" in target:
        for p in [".text$", ".rdata$", ".data$", ".bss$", ".pdata$", ".xdata$", ".tls$"]:
            if name.startswith(p) and name not in [".rdata$T", ".rdata$zzz", ".tls$", ".tls$ZZZ"]:
                return p + "<sym>"
    return name

def scan_target_objects(target: str, obj_paths: list[Path]):
    relocs = Counter()
    sections = Counter()
    sec_types = Counter()
    sym_bindings = Counter()
    sym_types = Counter()
    sym_vis = Counter()
    comdat_kinds = Counter()
    loh_kinds = Counter()
    feat00_vals = Counter()
    drectve_flags = Counter()

    # Batch llvm-readobj calls in chunks of 60 objects
    chunk_size = 60
    for i in range(0, len(obj_paths), chunk_size):
        chunk = [str(p) for p in obj_paths[i:i+chunk_size]]
        cmd = [
            LLVM_READOBJ, "--sections", "--symbols", "--relocations",
            "--elf-section-groups", "--coff-directives"
        ] + chunk
        out = subprocess.run(cmd, text=True, capture_output=True, errors="replace").stdout

        # Relocations
        for m in re.finditer(r"0x[0-9A-Fa-f]+\s+([A-Z0-9_]+(?:_[A-Z0-9]+)+)\s+", out):
            rk = m.group(1)
            if rk.startswith(("R_X86_64_", "R_386_", "R_AARCH64_", "ARM64_RELOC_", "IMAGE_REL_")):
                relocs[rk] += 1

        # Sections
        if "apple-darwin" in target:
            for m in re.finditer(r"Section \{\s+Index: \d+\s+Name: ([^\s(]+)[^\n]*\n\s+Segment: ([^\s(]+)", out):
                sections[f"{m.group(2)},{m.group(1)}"] += 1
            for m in re.finditer(r"Type: ([A-Za-z0-9_]+ \(0x[0-9A-Fa-f]+\))", out):
                sec_types[m.group(1)] += 1
        elif "windows" in target:
            for m in re.finditer(r"Section \{\s+Number: \d+\s+Name: ([^\s(]+)", out):
                sections[normalize_sec(m.group(1), target)] += 1
            for m in re.finditer(r"Selection: ([A-Za-z0-9_]+ \(0x[0-9A-Fa-f]+\))", out):
                comdat_kinds[m.group(1)] += 1
            for m in re.finditer(r"Name: @feat\.00\s+Value: (\d+)", out):
                feat00_vals[f"0x{int(m.group(1)):x}"] += 1
            for m in re.finditer(r"Directive\(s\): ([^\n]+)", out):
                for tok in m.group(1).strip().split():
                    prefix = tok.split(":")[0] if ":" in tok else tok
                    drectve_flags[prefix] += 1
        else:
            for m in re.finditer(r"Section \{\s+Index: \d+\s+Name: ([^\s(]+)[^\n]*\n\s+Type: ([^\n]+)", out):
                sname = m.group(1)
                if sname and sname != "<Not":
                    sections[normalize_sec(sname, target)] += 1
                    sec_types[m.group(2).strip()] += 1
            for m in re.finditer(r"Type: COMDAT \(0x1\)", out):
                comdat_kinds["GRP_COMDAT (0x1)"] += 1

        # Symbols
        for m in re.finditer(r"Binding: ([^\n]+)", out):
            sym_bindings[m.group(1).strip()] += 1
        for m in re.finditer(r"StorageClass: ([^\n]+)", out):
            sym_bindings[m.group(1).strip()] += 1
        for m in re.finditer(r"Symbol \{\s+Name: [^\n]+\n\s+Value: [^\n]+\n\s+Size: \d+\n\s+Binding: [^\n]+\n\s+Type: ([^\n]+)\n\s+Other: ([^\n]+)", out):
            sym_types[m.group(1).strip()] += 1
            sym_vis[m.group(2).strip()] += 1
        if "apple-darwin" in target:
            for m in re.finditer(r"Symbol \{\s+Name: [^\n]+\n\s+Type: ([^\n]+)", out):
                sym_types[m.group(1).strip()] += 1

    if "apple-darwin" in target:
        for i in range(0, len(obj_paths), chunk_size):
            chunk = [str(p) for p in obj_paths[i:i+chunk_size]]
            out_loh = subprocess.run([LLVM_OBJDUMP, "--macho", "--loh"] + chunk, text=True, capture_output=True, errors="replace").stdout
            for m in re.finditer(r"\b(LOH_[A-Z0-9_]+)\b", out_loh):
                loh_kinds[m.group(1)] += 1

    return {
        "num_objects": len(obj_paths),
        "total_relocations": sum(relocs.values()),
        "distinct_relocation_kinds": len(relocs),
        "relocations": dict(relocs.most_common()),
        "sections": dict(sections.most_common(40)),
        "section_types": dict(sec_types.most_common()),
        "symbol_bindings": dict(sym_bindings.most_common()),
        "symbol_types": dict(sym_types.most_common()),
        "symbol_visibilities": dict(sym_vis.most_common()),
        "comdat_kinds": dict(comdat_kinds.most_common()),
        "loh_kinds": dict(loh_kinds.most_common()),
        "feat00_values": dict(feat00_vals.most_common()),
        "drectve_prefixes": dict(drectve_flags.most_common()),
    }

def main():
    work = OUT_DIR / "tmp" / "t8_census_work"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)

    # 1. Extract sample crates once
    cache_roots = glob.glob("/usr/local/google/home/joshlf/.cargo/registry/cache/*")
    crate_srcs = []
    crates_dir = work / "crates_src"
    crates_dir.mkdir()
    for cname, entry_rel, edition, cfg_args in SAMPLE_CRATES:
        matches = []
        for cr in cache_roots:
            matches.extend(glob.glob(f"{cr}/{cname}"))
        if not matches:
            print(f"Warning: {cname} not found in cargo cache")
            continue
        cpath = matches[0]
        dest = crates_dir / cname.replace(".crate", "")
        dest.mkdir()
        with tarfile.open(cpath, "r:gz") as tf:
            tf.extractall(dest, filter="data")
        inner = next(dest.iterdir())
        crate_srcs.append((cname.split("-")[0].replace("-", "_"), inner / entry_rel, edition, cfg_args))
    print(f"Prepared {len(crate_srcs)} sample crates: {[c[0] for c in crate_srcs]}")

    def process_target(t: str):
        t_work = work / t
        t_work.mkdir(parents=True)
        # Extract all .rlib files in sysroot for target t
        rlib_dir = SYSROOT / "lib/rustlib" / t / "lib"
        sys_objs_dir = t_work / "sys_objs"
        sys_objs_dir.mkdir()
        sys_objs = []
        for rlib in sorted(rlib_dir.glob("*.rlib")):
            sub = sys_objs_dir / rlib.stem
            sub.mkdir()
            subprocess.run([LLVM_AR, "x", str(rlib)], cwd=str(sub), check=True)
            for o in sorted(sub.glob("*.o")):
                sys_objs.append(o)

        # Compile sample crates for target t
        sample_objs_dir = t_work / "sample_objs"
        sample_objs_dir.mkdir()
        sample_objs = []
        for cname, lib_rs, edition, cfg_args in crate_srcs:
            out_o = sample_objs_dir / f"{cname}.o"
            cmd = [
                RUSTC, "+1.99.1", "--target", t, "--crate-type=rlib",
                "--emit=obj", "--edition", edition, "-C", "opt-level=3",
                "-C", "codegen-units=1", str(lib_rs), "-o", str(out_o)
            ] + cfg_args
            res = subprocess.run(cmd, cwd=str(lib_rs.parent.parent), capture_output=True, text=True)
            if res.returncode == 0 and out_o.exists():
                sample_objs.append(out_o)
            else:
                print(f"Failed {cname} on {t}: {res.stderr[:200]}")

        sys_stats = scan_target_objects(t, sys_objs)
        sample_stats = scan_target_objects(t, sample_objs)
        print(f"Finished {t}: sys_objs={len(sys_objs)} ({sys_stats['total_relocations']} relocs), sample_objs={len(sample_objs)} ({sample_stats['total_relocations']} relocs)")
        return t, {"sysroot_rlibs": sys_stats, "crate_sample_o3": sample_stats}

    full_results = {}
    with ThreadPoolExecutor(max_workers=8) as ex:
        for t, res in ex.map(process_target, TARGETS):
            full_results[t] = res

    out_json = OUT_DIR / "t8_full_census.json"
    out_json.write_text(json.dumps(full_results, indent=2))
    print("Saved full T8 census to", out_json)

if __name__ == "__main__":
    main()
