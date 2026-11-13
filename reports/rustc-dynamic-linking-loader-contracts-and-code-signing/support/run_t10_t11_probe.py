#!/usr/bin/env python3
import glob, json, os, re, shutil, subprocess
from pathlib import Path

SYSROOT = Path("/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu")
BIN_DIR = SYSROOT / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
GCC_LD_DIR = BIN_DIR / "gcc-ld"
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

def inspect_prebuilt_std_dylibs():
    res = {}
    for t in TARGETS:
        ldir = SYSROOT / "lib/rustlib" / t / "lib"
        dylibs = list(ldir.glob("libstd-*.so")) + list(ldir.glob("libstd-*.dylib")) + list(ldir.glob("std-*.dll"))
        if not dylibs:
            print(f"No prebuilt std dylib for {t}")
            continue
        p = dylibs[0]
        ro = subprocess.check_output([
            LLVM_READOBJ, "--file-headers", "--program-headers", "--sections",
            "--dynamic-table", "--relocations", "--coff-imports", "--coff-exports",
            "--coff-tls-directory", "--coff-load-config", str(p)
        ], text=True, errors="replace")

        extra = ""
        if "apple-darwin" in t:
            extra = subprocess.check_output([
                LLVM_OBJDUMP, "--macho", "--private-headers", "--dylibs-used",
                "--rpaths", "--chained-fixups", str(p)
            ], text=True, errors="replace")[:8000]

        res[t] = {
            "filename": p.name,
            "size_bytes": p.stat().st_size,
            "readobj_head": ro[:6000],
            "readobj_relocs_summary": dict(),
            "extra_head": extra[:4000],
        }
        # Count dynamic relocations in libstd shared library
        relocs = {}
        for m in re.finditer(r"\b(R_X86_64_[A-Z0-9_]+|R_386_[A-Z0-9_]+|R_AARCH64_[A-Z0-9_]+|IMAGE_REL_BASED_[A-Z0-9_]+)\b", ro):
            k = m.group(1)
            relocs[k] = relocs.get(k, 0) + 1
        res[t]["readobj_relocs_summary"] = relocs
        print(f"Prebuilt std dylib {t}: {p.name} ({p.stat().st_size} bytes), dyn_relocs={relocs}")
    return res

if __name__ == "__main__":
    out = inspect_prebuilt_std_dylibs()
    (OUT_DIR / "t10_std_dylibs.json").write_text(json.dumps(out, indent=2))
