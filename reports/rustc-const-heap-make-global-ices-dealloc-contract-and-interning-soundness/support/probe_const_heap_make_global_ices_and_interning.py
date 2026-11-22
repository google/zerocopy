#!/usr/bin/env python3
"""Reproducible rustc + Miri probe for #![feature(const_heap)] ICEs,
const_deallocate # Safety contract contradictions, and CTFE vs. runtime/Miri
intrinsic fallback divergence.

Uses only the Python 3.10+ standard library and temporary directories.
"""

from __future__ import annotations

import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path


RUSTC_SRC_RE = re.compile(r"/rustc(?:-dev)?/[0-9a-f]{40}/")
PID_RE = re.compile(r"thread 'rustc' \(\d+\)")


def scrub(text: str, tmpdir: str) -> str:
    text = text.replace(tmpdir, "<TMP>")
    text = text.replace(str(Path.home()), "<HOME>")
    text = RUSTC_SRC_RE.sub("<RUSTC_SRC>/", text)
    text = PID_RE.sub("thread 'rustc' (<PID>)", text)
    return text


def find_bin(name: str) -> str:
    found = shutil.which(name)
    if found:
        return found
    candidate = Path.home() / ".cargo" / "bin" / name
    if candidate.exists():
        return str(candidate)
    raise RuntimeError(f"Could not find `{name}` in PATH or ~/.cargo/bin")


def run_rustc_case(
    rustc: str, tmpdir: Path, name: str, code: str, extra_args: list[str] | None = None
) -> dict:
    src = tmpdir / f"{name}.rs"
    out = tmpdir / f"lib{name}.rlib"
    src.write_text(code, encoding="utf-8")
    cmd = [rustc, "--crate-type=lib", "--edition=2024", str(src), "-o", str(out)]
    if extra_args:
        cmd.extend(extra_args)
    proc = subprocess.run(cmd, capture_output=True, text=True, timeout=60)
    stderr_scrubbed = scrub(proc.stderr, str(tmpdir))
    lines = stderr_scrubbed.splitlines()
    stderr_head = "\n".join(lines[:16])
    is_ice = (
        proc.returncode == 101
        or "internal compiler error" in stderr_scrubbed
        or "thread 'rustc'" in stderr_scrubbed
    )
    return {
        "rc": proc.returncode,
        "is_ice": is_ice,
        "stderr_head": stderr_head,
    }


CORE_CASES: list[tuple[str, str, list[str]]] = [
    (
        "valid_const_reborrowed_shared_ref",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const C: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    &*core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
    (
        "valid_static_reborrowed_shared_ref",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub static S: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    &*core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
    (
        "ice1a_const_raw_ptr_from_const_make_global",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const RAW_FROM_MAKE_GLOBAL: *const u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
    (
        "ice1b_static_raw_ptr_from_const_make_global",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
#[repr(transparent)]
pub struct SyncPtr(pub *const u8);
unsafe impl Sync for SyncPtr {}
pub static STATIC_RAW: SyncPtr = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    SyncPtr(core::intrinsics::const_make_global(p))
};
""",
        [],
    ),
    (
        "reborrow_to_raw_ptr_avoids_ice1",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const RAW_REBORROWED: *const u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    (&*core::intrinsics::const_make_global(p)) as *const u8
};
""",
        [],
    ),
    (
        "ice2a_static_mut_reborrowed_ref",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub static mut SM_REF: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    &*core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
    (
        "ice2b_static_mut_raw_ptr",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub static mut SM_RAW: *const u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
    (
        "doc_contradiction_dealloc_stack_local",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const DEALLOC_LOCAL: u8 = unsafe {
    let mut x: u8 = 7;
    core::intrinsics::const_deallocate(&raw mut x, 1, 1);
    x
};
""",
        [],
    ),
    (
        "dealloc_other_const_memory_is_noop",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
const OTHER: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 9;
    &*core::intrinsics::const_make_global(p)
};
pub const DEALLOC_OTHER: u8 = unsafe {
    core::intrinsics::const_deallocate(OTHER as *const u8 as *mut u8, 1, 1);
    *OTHER
};
""",
        [],
    ),
    (
        "dealloc_static_item_throws_ub",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
static STAT: u8 = 1;
pub const DEALLOC_STAT: u8 = unsafe {
    core::intrinsics::const_deallocate(&raw const STAT as *mut u8, 1, 1);
    0
};
""",
        [],
    ),
    (
        "dealloc_same_const_after_make_global_throws_ub",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const DEALLOC_SAME_GLOBAL: u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 5;
    let _g = core::intrinsics::const_make_global(p);
    core::intrinsics::const_deallocate(p, 1, 1);
    0
};
""",
        [],
    ),
    (
        "uninterned_transient_const_allocate_rejected",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const TRANSIENT_LEAK: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 5;
    &*p
};
""",
        [],
    ),
    (
        "make_global_nonzero_offset_rejected",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const OFFSET_ERR: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(2, 1);
    *p = 1;
    *p.add(1) = 2;
    &*core::intrinsics::const_make_global(p.add(1))
};
""",
        [],
    ),
    (
        "make_global_twice_rejected",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const TWICE_ERR: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 1;
    let _ = core::intrinsics::const_make_global(p);
    &*core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
    (
        "thread_local_nested_static_rejected",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics, thread_local)]
#[thread_local]
pub static TLS_REF: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    &*core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
]


EXTENDED_CASES: list[tuple[str, str, list[str]]] = [
    (
        "ice1a_with_unleash_miri_downgrades_to_normal_error",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const RAW_UNLEASH: *const u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    core::intrinsics::const_make_global(p)
};
""",
        ["-Z", "unleash-the-miri-inside-of-you"],
    ),
    (
        "ice2a_with_unleash_miri_still_ices",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub static mut SM_UNLEASH: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    &*core::intrinsics::const_make_global(p)
};
""",
        ["-Z", "unleash-the-miri-inside-of-you"],
    ),
    (
        "static_mut_preinterned_const_avoids_ice2",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
const PRE: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    &*core::intrinsics::const_make_global(p)
};
pub static mut SM_PRE: &'static u8 = PRE;
""",
        [],
    ),
    (
        "static_mut_uninterned_transient_rejected_not_ice",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub static mut SM_TRANSIENT: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 5;
    &*p
};
""",
        [],
    ),
    (
        "static_mut_raw_ptr_via_preinterned_const_avoids_both_ices",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
const PRE_RAW: *const u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    (&*core::intrinsics::const_make_global(p)) as *const u8
};
pub static mut SM_PRE_RAW: *const u8 = PRE_RAW;
""",
        [],
    ),
    (
        "reborrow_cell_nonfreeze_to_raw_ptr_avoids_ice1",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
use core::cell::Cell;
pub const CELL_RAW: *const Cell<u8> = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    let g = core::intrinsics::const_make_global(p) as *const Cell<u8>;
    (&*g) as *const Cell<u8>
};
""",
        [],
    ),
    (
        "pre_call_alias_after_make_global_still_triggers_ice1",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const ALIAS_RAW: *const u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 42;
    let _g = core::intrinsics::const_make_global(p);
    p as *const u8
};
""",
        [],
    ),
    (
        "dealloc_other_const_wrong_size_is_noop",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
const OTHER: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 9;
    &*core::intrinsics::const_make_global(p)
};
pub const DEALLOC_OTHER_BAD_SIZE: u8 = unsafe {
    core::intrinsics::const_deallocate(OTHER as *const u8 as *mut u8, 999, 1);
    *OTHER
};
""",
        [],
    ),
    (
        "dealloc_other_const_bad_align_throws_ub_before_skip",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
const OTHER: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 9;
    &*core::intrinsics::const_make_global(p)
};
pub const DEALLOC_OTHER_BAD_ALIGN: u8 = unsafe {
    core::intrinsics::const_deallocate(OTHER as *const u8 as *mut u8, 1, 3);
    *OTHER
};
""",
        [],
    ),
    (
        "make_global_on_stack_local_rejected",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const STACK_MAKE_GLOBAL: &'static u8 = unsafe {
    let mut x: u8 = 7;
    &*core::intrinsics::const_make_global(&raw mut x)
};
""",
        [],
    ),
    (
        "make_global_on_dangling_heap_rejected",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const DANGLING_MAKE_GLOBAL: &'static u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 7;
    core::intrinsics::const_deallocate(p, 1, 1);
    &*core::intrinsics::const_make_global(p)
};
""",
        [],
    ),
    (
        "write_after_make_global_throws_ub",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const WRITE_AFTER_GLOBAL: u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 7;
    let _g = core::intrinsics::const_make_global(p);
    *p = 8;
    *p
};
""",
        [],
    ),
    (
        "transient_alloc_write_read_dealloc_succeeds",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const TRANSIENT_OK: u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 55;
    let v = *p;
    core::intrinsics::const_deallocate(p, 1, 1);
    v
};
""",
        [],
    ),
    (
        "transient_alloc_unreachable_leak_silently_dropped",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const UNREACHABLE_LEAK_OK: u8 = unsafe {
    let p = core::intrinsics::const_allocate(1, 1);
    *p = 55;
    *p
};
""",
        [],
    ),
    (
        "const_allocate_bad_align_throws_ub_in_ctfe",
        """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
pub const BAD_ALIGN_ALLOC: u8 = unsafe {
    let _p = core::intrinsics::const_allocate(1, 3);
    0
};
""",
        [],
    ),
]


DUAL_NATIVE_RS = """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]

const unsafe fn probe_dual() -> (bool, u8) {
    unsafe {
        let p = core::intrinsics::const_allocate(1, 1);
        if !p.is_null() {
            *p = 88;
            let gp = core::intrinsics::const_make_global(p);
            (true, *gp)
        } else {
            let mut x: u8 = 77;
            // At runtime AND under Miri (#[miri::intrinsic_fallback_is_spec]):
            // const_deallocate skips align (3 != 2^k), size (999), and kind (stack local),
            // const_allocate(1, 3) skips align validation and returns null_mut(),
            // and const_make_global is the identity function on any pointer.
            core::intrinsics::const_deallocate(&raw mut x, 999, 3);
            let bad_alloc = core::intrinsics::const_allocate(1, 3);
            let gp = core::intrinsics::const_make_global(&raw mut x);
            (bad_alloc.is_null() && !gp.is_null(), *gp)
        }
    }
}

const CTFE_VAL: (bool, u8) = unsafe { probe_dual() };

fn main() {
    let rt_val = unsafe { probe_dual() };
    println!("CTFE={CTFE_VAL:?} RUNTIME={rt_val:?}");
}
"""


DUAL_MIRI_NOSTD_RS = """#![allow(internal_features)]
#![feature(const_heap, core_intrinsics)]
#![no_std]
#![no_main]

use core::fmt::Write as _;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    core::intrinsics::abort()
}

unsafe extern "C" {
    fn write(fd: i32, buf: *const u8, count: usize) -> isize;
}

struct StackBuf {
    buf: [u8; 128],
    len: usize,
}

impl core::fmt::Write for StackBuf {
    fn write_str(&mut self, s: &str) -> core::fmt::Result {
        let bytes = s.as_bytes();
        let end = self.len + bytes.len();
        if end > self.buf.len() {
            return Err(core::fmt::Error);
        }
        self.buf[self.len..end].copy_from_slice(bytes);
        self.len = end;
        Ok(())
    }
}

const unsafe fn probe_dual() -> (bool, u8) {
    unsafe {
        let p = core::intrinsics::const_allocate(1, 1);
        if !p.is_null() {
            *p = 88;
            let gp = core::intrinsics::const_make_global(p);
            (true, *gp)
        } else {
            let mut x: u8 = 77;
            core::intrinsics::const_deallocate(&raw mut x, 999, 3);
            let bad_alloc = core::intrinsics::const_allocate(1, 3);
            let gp = core::intrinsics::const_make_global(&raw mut x);
            (bad_alloc.is_null() && !gp.is_null(), *gp)
        }
    }
}

const CTFE_VAL: (bool, u8) = unsafe { probe_dual() };

#[unsafe(no_mangle)]
fn miri_start(_argc: isize, _argv: *const *const u8) -> isize {
    let rt_val = unsafe { probe_dual() };
    let mut out = StackBuf { buf: [0; 128], len: 0 };
    let _ = writeln!(out, "CTFE={CTFE_VAL:?} RUNTIME={rt_val:?}");
    unsafe {
        write(1, out.buf.as_ptr(), out.len);
    }
    0
}
"""


def build_offline_miri_core_sysroot(rustc: str, sysroot: Path, tmpdir: Path) -> Path:
    host = None
    for line in subprocess.run([rustc, "-Vv"], capture_output=True, text=True, check=True).stdout.splitlines():
        if line.startswith("host:"):
            host = line.split(":", 1)[1].strip()
            break
    assert host is not None, "could not parse rustc host"
    miri_sysroot = tmpdir / "miri_sysroot"
    lib_dir = miri_sysroot / "lib" / "rustlib" / host / "lib"
    lib_dir.mkdir(parents=True, exist_ok=True)
    core_src = sysroot / "lib" / "rustlib" / "src" / "rust" / "library" / "core" / "src" / "lib.rs"
    env = os.environ.copy()
    env["RUSTC_BOOTSTRAP"] = "1"
    subprocess.run(
        [
            rustc,
            "--crate-name",
            "core",
            "--crate-type",
            "rlib",
            "--edition",
            "2024",
            "--cfg",
            "miri",
            "-Z",
            "always-encode-mir",
            "-Z",
            "force-unstable-if-unmarked",
            "-C",
            "panic=abort",
            "-C",
            "opt-level=0",
            str(core_src),
            "-o",
            str(lib_dir / "libcore.rlib"),
        ],
        env=env,
        capture_output=True,
        text=True,
        check=True,
        timeout=120,
    )
    cb_rs = tmpdir / "compiler_builtins_stub.rs"
    cb_rs.write_text(
        "#![allow(internal_features)]\n#![feature(no_core, compiler_builtins)]\n#![no_core]\n#![compiler_builtins]\n",
        encoding="utf-8",
    )
    subprocess.run(
        [
            rustc,
            "--crate-name",
            "compiler_builtins",
            "--crate-type",
            "rlib",
            "--edition",
            "2024",
            "-Z",
            "always-encode-mir",
            "-C",
            "panic=abort",
            str(cb_rs),
            "-o",
            str(lib_dir / "libcompiler_builtins.rlib"),
        ],
        env=env,
        capture_output=True,
        text=True,
        check=True,
        timeout=60,
    )
    return miri_sysroot


def run_dual_native_and_miri(rustc: str, tmpdir: Path) -> tuple[dict, dict, dict]:
    # Native binary
    main_rs = tmpdir / "dual_main.rs"
    bin_path = tmpdir / "dual_main"
    main_rs.write_text(DUAL_NATIVE_RS, encoding="utf-8")
    comp = subprocess.run(
        [rustc, "--edition=2024", str(main_rs), "-o", str(bin_path)],
        capture_output=True,
        text=True,
        timeout=60,
    )
    if comp.returncode == 0:
        run_proc = subprocess.run([str(bin_path)], capture_output=True, text=True, timeout=60)
        runtime_execution = {
            "compile_rc": comp.returncode,
            "run_rc": run_proc.returncode,
            "stdout": run_proc.stdout.strip(),
            "stderr_head": "\n".join(scrub(run_proc.stderr, str(tmpdir)).splitlines()[:15]),
        }
    else:
        runtime_execution = {
            "compile_rc": comp.returncode,
            "run_rc": None,
            "stdout": "",
            "stderr_head": "\n".join(scrub(comp.stderr, str(tmpdir)).splitlines()[:15]),
        }

    # Miri execution (Stacked Borrows default + Tree Borrows) via MIR-encoded core sysroot
    sysroot = Path(
        subprocess.run([rustc, "--print", "sysroot"], capture_output=True, text=True, check=True).stdout.strip()
    )
    miri_bin = sysroot / "bin" / "miri"
    miri_sysroot = build_offline_miri_core_sysroot(rustc, sysroot, tmpdir)
    miri_rs = tmpdir / "dual_miri.rs"
    miri_rs.write_text(DUAL_MIRI_NOSTD_RS, encoding="utf-8")

    env = os.environ.copy()
    ld_prev = env.get("LD_LIBRARY_PATH", "")
    env["LD_LIBRARY_PATH"] = f"{sysroot / 'lib'}:{ld_prev}" if ld_prev else str(sysroot / "lib")

    def run_miri_mode(extra_flags: list[str]) -> dict:
        proc = subprocess.run(
            [
                str(miri_bin),
                "--sysroot",
                str(miri_sysroot),
                "--edition=2024",
                "-C",
                "panic=abort",
                *extra_flags,
                str(miri_rs),
            ],
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        return {
            "rc": proc.returncode,
            "stdout": proc.stdout.strip(),
            "stderr_head": "\n".join(scrub(proc.stderr, str(tmpdir)).splitlines()[:15]),
        }

    miri_sb = run_miri_mode([])
    miri_tb = run_miri_mode(["-Zmiri-tree-borrows"])
    return runtime_execution, miri_sb, miri_tb


def main() -> int:
    rustc = find_bin("rustc")
    cargo = find_bin("cargo")
    rustc_vv = subprocess.run([rustc, "-Vv"], capture_output=True, text=True, check=True).stdout.strip()
    miri_v_proc = subprocess.run([cargo, "miri", "-V"], capture_output=True, text=True)
    miri_v = miri_v_proc.stdout.strip() if miri_v_proc.returncode == 0 else "unavailable"

    with tempfile.TemporaryDirectory(prefix="const_heap_probe_") as td:
        tmpdir = Path(td)
        matrix = {}
        for name, code, extra_args in CORE_CASES:
            matrix[name] = run_rustc_case(rustc, tmpdir, name, code, extra_args)

        extended_matrix = {}
        for name, code, extra_args in EXTENDED_CASES:
            extended_matrix[name] = run_rustc_case(rustc, tmpdir, name, code, extra_args)

        runtime_execution, miri_sb, miri_tb = run_dual_native_and_miri(rustc, tmpdir)

    result = {
        "rustc_version": rustc_vv,
        "miri_version": miri_v,
        "matrix": matrix,
        "extended_matrix": extended_matrix,
        "runtime_execution": runtime_execution,
        "miri_execution": miri_sb,
        "miri_tree_borrows_execution": miri_tb,
    }

    if len(sys.argv) > 1 and sys.argv[1] == "--out":
        out_path = Path(sys.argv[2])
        out_path.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    else:
        print(json.dumps(result, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
