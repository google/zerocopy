#!/usr/bin/env python3
import json, os, re, shutil, subprocess
from pathlib import Path

SYSROOT = Path("/usr/local/google/home/joshlf/.rustup/toolchains/1.99.1-x86_64-unknown-linux-gnu")
BIN_DIR = SYSROOT / "lib/rustlib/x86_64-unknown-linux-gnu/bin"
GCC_LD = BIN_DIR / "gcc-ld"
LLVM_READOBJ = str(BIN_DIR / "llvm-readobj")
LLVM_OBJDUMP = str(BIN_DIR / "llvm-objdump")
RUSTC = "rustc"
OUT_DIR = Path(".")

STD_PROBE_RS = r"""
use std::collections::HashMap;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex};
use std::thread;

static COUNTER: AtomicU64 = AtomicU64::new(100);

fn main() {
    let mut map = HashMap::new();
    map.insert("arch", std::env::consts::ARCH);
    map.insert("os", std::env::consts::OS);
    let shared = Arc::new(Mutex::new(Vec::new()));
    let s2 = Arc::clone(&shared);
    let h = thread::spawn(move || {
        let prev = COUNTER.fetch_add(42, Ordering::SeqCst);
        s2.lock().unwrap().push(prev);
        prev + 42
    });
    let res = h.join().unwrap();
    let caught = std::panic::catch_unwind(|| {
        if res == 0 { panic!("unreachable"); }
        res * 2
    }).unwrap();
    println!("OK arch={} os={} res={} caught={}", map["arch"], map["os"], res, caught);
}
"""

def check_dll_and_elf_headers():
    info = {}
    for t in ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu", "aarch64-unknown-linux-gnu"]:
        so = next((SYSROOT / f"lib/rustlib/{t}/lib").glob("libstd-*.so"))
        ro = subprocess.check_output([LLVM_READOBJ, "--program-headers", "--dynamic-table", str(so)], text=True)
        relro = "PT_GNU_RELRO" in ro
        bind_now = "BIND_NOW" in ro
        soname = re.findall(r"SONAME\s+Library soname: \[([^\]]+)\]", ro)
        needed = re.findall(r"NEEDED\s+Shared library: \[([^\]]+)\]", ro)
        info[t] = {"relro": relro, "bind_now": bind_now, "soname": soname, "needed": needed}
    for t in ["x86_64-pc-windows-msvc", "x86_64-pc-windows-gnu", "i686-pc-windows-msvc", "aarch64-pc-windows-msvc"]:
        dll = next((SYSROOT / f"lib/rustlib/{t}/lib").glob("std-*.dll"))
        ro = subprocess.check_output([LLVM_READOBJ, "--file-headers", str(dll)], text=True)
        m = re.search(r"DLLCharacteristics \[(.*?)\]", ro, re.DOTALL)
        chars = [x.strip() for x in m.group(1).splitlines() if x.strip()] if m else []
        info[t] = {"dll_characteristics": chars}
    print("=== Prebuilt std security/loader flags ===")
    print(json.dumps(info, indent=2))
    return info

def test_builds():
    work = OUT_DIR / "tmp/t11_work"
    if work.exists():
        shutil.rmtree(work)
    work.mkdir(parents=True)
    src = work / "std_probe.rs"
    src.write_text(STD_PROBE_RS)

    for t in ["x86_64-unknown-linux-gnu", "i686-unknown-linux-gnu"]:
        out_bin = work / f"std_probe_{t}"
        res = subprocess.run([RUSTC, "+1.99.1", "--target", t, "-C", "opt-level=2", str(src), "-o", str(out_bin)], text=True, capture_output=True)
        print(f"Build {t}: rc={res.returncode}, err={res.stderr[:200]}")
        if res.returncode == 0:
            run_native = subprocess.run([str(out_bin)], text=True, capture_output=True)
            print(f"  Run native {t}: rc={run_native.returncode}, out={run_native.stdout.strip()}")
            if t == "i686-unknown-linux-gnu":
                run_qemu = subprocess.run(["qemu-i386", str(out_bin)], text=True, capture_output=True)
                print(f"  Run qemu-i386 {t}: rc={run_qemu.returncode}, out={run_qemu.stdout.strip()}")

if __name__ == "__main__":
    check_dll_and_elf_headers()
    test_builds()
