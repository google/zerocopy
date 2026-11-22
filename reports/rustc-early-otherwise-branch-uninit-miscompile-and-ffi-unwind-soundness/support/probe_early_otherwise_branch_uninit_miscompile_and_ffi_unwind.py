#!/usr/bin/env python3
"""Differential rustc / Miri probe for three rustc MIR-level mechanisms.

  1. EarlyOtherwiseBranch hoisting a scalar read onto a path where the read
     place is uninitialized or has no live storage.
  2. SimplifyComparisonIntegral rewriting `_t = Eq/Ne(move _x, const K);
     switchInt(_t)` into a switch on `_x`.
  3. `required_panic_strategy` / `has_ffi_unwind_calls` deciding which
     `-C panic=unwind` rlibs may be linked into a `-C panic=abort` binary.

The script only records observations. It writes every Rust input into a
temporary directory, runs the given `rustc` (and, optionally, the `miri`
driver) on it, and emits one JSON document. It makes no assumption about
which toolchain it is pointed at; the toolchain identity is recorded from
`rustc -Vv` in the output.

Usage:
    python3 probe_early_otherwise_branch_uninit_miscompile_and_ffi_unwind.py \
        --rustc /path/to/nightly/bin/rustc \
        [--miri /path/to/nightly/bin/miri --miri-sysroot /path/to/miri/sysroot] \
        [--out results.json]

A nightly toolchain is required (`-Z` flags, `custom_mir`). The Miri part is
skipped when `--miri` is not given. `--miri-sysroot` must name a sysroot built
by `cargo miri setup` for the same toolchain.

Only the Python standard library is used.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

# --------------------------------------------------------------------------
# Rust inputs
# --------------------------------------------------------------------------

# A local that is never written. The function is free of undefined behavior
# exactly for inputs other than 1 and 2 (those two inputs read the local).
# The probe only calls it with 99.
EOB_NEVER_INIT = r'''
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, unused_assignments, unused_variables)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
#[no_mangle]
pub fn eob_silicon_miscompile(q: u32) -> u32 {
    mir! {
        let uninit_local: u32;
        {
            match q {
                1 => bb1,
                2 => bb2,
                _ => bb5,
            }
        }
        bb1 = {
            match uninit_local {
                1 => bb3,
                _ => bb5,
            }
        }
        bb2 = {
            match uninit_local {
                2 => bb4,
                _ => bb5,
            }
        }
        bb3 = {
            RET = 10;
            Return()
        }
        bb4 = {
            RET = 20;
            Return()
        }
        bb5 = {
            RET = 42;
            Return()
        }
    }
}

fn main() {
    let q = core::hint::black_box(99u32);
    println!("OUT={}", eob_silicon_miscompile(q));
}
'''

# A local whose storage is live (and initialized) on every path except the one
# taken for q == 99. The function is free of undefined behavior for EVERY
# input: the local is only read under q == 1 or q == 2, where it is live and
# initialized.
EOB_DEAD_LOCAL = r'''
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, unused_assignments, unused_variables)]
use core::intrinsics::mir::*;

#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
#[no_mangle]
pub fn eob_dead_local_ub(q: u32) -> u32 {
    mir! {
        let dead_on_99: u32;
        {
            match q {
                99 => parent,
                _ => alloc,
            }
        }
        alloc = {
            StorageLive(dead_on_99);
            dead_on_99 = q;
            Goto(parent)
        }
        parent = {
            match q {
                1 => bb1,
                2 => bb2,
                _ => bb5,
            }
        }
        bb1 = {
            match dead_on_99 {
                1 => bb3,
                _ => bb5,
            }
        }
        bb2 = {
            match dead_on_99 {
                2 => bb4,
                _ => bb5,
            }
        }
        bb3 = {
            StorageDead(dead_on_99);
            RET = 10;
            Return()
        }
        bb4 = {
            StorageDead(dead_on_99);
            RET = 20;
            Return()
        }
        bb5 = {
            StorageDead(dead_on_99);
            RET = 42;
            Return()
        }
    }
}

fn main() {
    for q in [99u32, 1, 2, 7] {
        println!("OUT({})={}", q, eob_dead_local_ub(core::hint::black_box(q)));
    }
}
'''

# The custom-MIR reproducer from the upstream bug report
# rust-lang/rust issue 164765, with the single call replaced by a loop that
# prints every result. `x` is written before every read, so the function is
# free of undefined behavior for every input.
EOB_UPSTREAM_CUSTOM_MIR = r'''
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, unused_assignments)]

use std::hint::black_box;
use std::intrinsics::mir::*;

#[custom_mir(dialect = "runtime")]
#[inline(never)]
#[no_mangle]
fn foo(q: u64) -> u64 {
    mir! {
        let x: u64;
        {
            match q {
                1 => init1,
                2 => init2,
                _ => parent,
            }
        }
        init1 = {
            x = 1;
            Goto(parent)
        }
        init2 = {
            x = 2;
            Goto(parent)
        }
        parent = {
            match q {
                1 => bb1,
                2 => bb2,
                _ => bb5,
            }
        }
        bb1 = {
            match x {
                1 => bb3,
                _ => bb5,
            }
        }
        bb2 = {
            match x {
                2 => bb4,
                _ => bb5,
            }
        }
        bb3 = {
            RET = 100;
            Return()
        }
        bb4 = {
            RET = 200;
            Return()
        }
        bb5 = {
            RET = 999;
            Return()
        }
    }
}

fn main() {
    for q in [0u64, 1, 2, 3, u64::MAX] {
        println!("foo({})={}", q, foo(black_box(q)));
    }
}
'''

# Surface Rust, no feature gates. This is the body of the upstream regression
# test `tests/ui/mir/hoist_uninit_early_else.rs` (added by rust-lang/rust pull
# request 164864), with the `assert_eq!` replaced by a `println!` so that a
# wrong result is recorded instead of aborting the run.
EOB_SURFACE_UNION = r'''
use std::hint::black_box;

union U {
    a: u64,
    b: (),
}

#[inline(never)]
#[no_mangle]
fn foo(q: u64) -> u64 {
    let mut u = U { b: () };
    match q {
        1 => u.a = 1,
        2 => u.a = 2,
        _ => {}
    }
    black_box(());
    let mut r = 999;
    // SAFETY: Each read of `u.a` is preceded by its initialization for the same value of `q`.
    unsafe {
        match q {
            1 => match u.a {
                1 => r = 100,
                _ => {}
            },
            2 => match u.a {
                2 => r = 200,
                _ => {}
            },
            _ => {}
        }
    }
    r
}

fn main() {
    for q in [0u64, 1, 2, 3, u64::MAX] {
        println!("foo({})={}", q, foo(black_box(q)));
    }
}
'''

# Surface Rust reproducer from upstream issue rust-lang/rust 159591: the read
# place is `*p`, which is not a stable-offset place.
EOB_SURFACE_DEREF = r'''
use std::hint::black_box;

#[inline(never)]
#[no_mangle]
unsafe fn foo(q: u64, p: *const u64) -> u64 {
    'a: {
        match q {
            1 => match *p { 1 => break 'a 100, _ => {} },
            2 => match *p { 2 => break 'a 200, _ => {} },
            _ => {}
        }
        999
    }
}

fn main() {
    let q: u64 = black_box(3);
    let p: *const u64 = black_box(std::ptr::null());
    let r = unsafe { foo(q, p) };
    println!("foo(3,null)={}", black_box(r));
}
'''

SCI = r'''
#![feature(custom_mir, core_intrinsics)]
#![allow(internal_features, unused_assignments, unused_variables)]
use core::intrinsics::mir::*;

// S1: `_t = Eq(move _x, const 43); switchInt(copy _t)`.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
pub fn sci_move_cmp_copy_switch(x: i32) -> i32 {
    mir! {
        let t: bool;
        {
            t = Move(x) == 43_i32;
            match t {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = { RET = 1; Return() }
        bb2 = { RET = 0; Return() }
    }
}

// S2: `_t = Ne(move _x, const 43); switchInt(move _t)`.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
pub fn sci_move_cmp_move_switch(x: i32) -> i32 {
    mir! {
        let t: bool;
        {
            t = Move(x) != 43_i32;
            match Move(t) {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = { RET = 1; Return() }
        bb2 = { RET = 0; Return() }
    }
}

// S3: a `StorageDead` of the compared local sits between the comparison and
// the switch.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
pub fn sci_storage_dead_between(x: i32) -> i32 {
    mir! {
        let y: i32;
        let t: bool;
        {
            StorageLive(y);
            y = x;
            t = Move(y) == 43_i32;
            StorageDead(y);
            match t {
                true => bb1,
                _ => bb2,
            }
        }
        bb1 = { RET = 1; Return() }
        bb2 = { RET = 0; Return() }
    }
}

// S4: the shape the pass would produce if it did NOT downgrade `Move` to
// `Copy`: `_t = Eq(move _x, const 43); switchInt(move _x)`. Written by hand.
#[custom_mir(dialect = "runtime", phase = "post-cleanup")]
#[inline(never)]
pub fn sci_hand_written_double_move(x: i32) -> i32 {
    mir! {
        let t: bool;
        {
            t = Move(x) == 43_i32;
            match Move(x) {
                43 => bb1,
                _ => bb2,
            }
        }
        bb1 = { RET = 1; Return() }
        bb2 = { RET = 0; Return() }
    }
}

fn main() {
    for x in [43_i32, 7] {
        let x = core::hint::black_box(x);
        println!(
            "x={} S1={} S2={} S3={} S4={}",
            x,
            sci_move_cmp_copy_switch(x),
            sci_move_cmp_move_switch(x),
            sci_storage_dead_between(x),
            sci_hand_written_double_move(x),
        );
    }
}
'''

SCI_FNS = [
    "sci_move_cmp_copy_switch",
    "sci_move_cmp_move_switch",
    "sci_storage_dead_between",
    "sci_hand_written_double_move",
]

# Upstream crates for the panic-strategy link matrix. Every one of them is
# compiled as an rlib named `ffi_up` exposing `pub fn entry(u32) -> u32`.
FFI_UP = {
    "pure_rust": r'''
#![crate_type = "rlib"]
pub fn entry(x: u32) -> u32 { x.wrapping_add(1) }
''',
    "c_unwind_foreign_call": r'''
#![crate_type = "rlib"]
extern "C-unwind" { fn may_throw(x: u32) -> u32; }
pub fn entry(x: u32) -> u32 { unsafe { may_throw(x) } }
''',
    "c_foreign_call": r'''
#![crate_type = "rlib"]
extern "C" { fn may_throw(x: u32) -> u32; }
pub fn entry(x: u32) -> u32 { unsafe { may_throw(x) } }
''',
    "c_unwind_foreign_call_inside_extern_c_body": r'''
#![crate_type = "rlib"]
extern "C-unwind" { fn may_throw(x: u32) -> u32; }
pub extern "C" fn guarded(x: u32) -> u32 { unsafe { may_throw(x) } }
pub fn entry(x: u32) -> u32 { guarded(x) }
''',
    "c_unwind_fn_pointer_call": r'''
#![crate_type = "rlib"]
pub fn call_ptr(f: unsafe extern "C-unwind" fn(u32) -> u32, x: u32) -> u32 { unsafe { f(x) } }
extern "C-unwind" fn local_impl(x: u32) -> u32 { x }
pub fn entry(x: u32) -> u32 { call_ptr(local_impl, x) }
''',
    "c_unwind_rust_defined_callee": r'''
#![crate_type = "rlib"]
#[inline(never)]
pub extern "C-unwind" fn rust_defined(x: u32) -> u32 { x }
pub fn entry(x: u32) -> u32 { rust_defined(x) }
''',
    "inline_asm_may_unwind": r'''
#![crate_type = "rlib"]
#![feature(asm_unwind)]
pub fn entry(x: u32) -> u32 {
    unsafe { core::arch::asm!("nop", options(may_unwind)); }
    x
}
''',
}

FFI_DOWN = r'''
extern crate ffi_up;
#[no_mangle]
pub extern "C-unwind" fn may_throw(x: u32) -> u32 { x }
fn main() { println!("OUT={}", ffi_up::entry(core::hint::black_box(41))); }
'''

# `#![no_std]` variant of the `c_unwind_foreign_call` pairing. No crate in this
# link is a panic runtime (`panic_unwind` / `panic_abort` are only pulled in
# through `std`).
FFI_NO_STD_UP = r'''
#![crate_type = "rlib"]
#![no_std]
extern "C-unwind" { fn may_throw(x: u32) -> u32; }
pub fn entry(x: u32) -> u32 { unsafe { may_throw(x) } }
'''

FFI_NO_STD_DOWN = r'''
#![no_std]
#![no_main]
extern crate ffi_up;

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! { loop {} }

#[no_mangle]
pub extern "C-unwind" fn may_throw(x: u32) -> u32 { x }

#[no_mangle]
pub extern "C" fn main() -> i32 {
    if ffi_up::entry(core::hint::black_box(41)) == 41 { 0 } else { 1 }
}
'''

# (upstream crate, upstream -C panic, downstream -C panic)
FFI_MATRIX = [
    ("pure_rust", "unwind", "abort"),
    ("c_unwind_foreign_call", "unwind", "abort"),
    ("c_foreign_call", "unwind", "abort"),
    ("c_unwind_foreign_call_inside_extern_c_body", "unwind", "abort"),
    ("c_unwind_fn_pointer_call", "unwind", "abort"),
    ("c_unwind_rust_defined_callee", "unwind", "abort"),
    ("inline_asm_may_unwind", "unwind", "abort"),
    ("c_unwind_foreign_call", "unwind", "unwind"),
    ("c_unwind_foreign_call", "abort", "abort"),
    ("c_unwind_foreign_call", "abort", "unwind"),
    ("pure_rust", "abort", "unwind"),
    ("pure_rust", "abort", "abort"),
]

# --------------------------------------------------------------------------
# Helpers
# --------------------------------------------------------------------------

SCRUB = []  # (needle, replacement) pairs applied to all captured text


def scrub(text):
    for needle, repl in SCRUB:
        if needle:
            text = text.replace(needle, repl)
    return text


def run(cmd, cwd, timeout=300):
    try:
        p = subprocess.run(
            cmd, cwd=cwd, stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, timeout=timeout,
        )
        rc = p.returncode
        out = p.stdout.decode("utf-8", "replace")
        err = p.stderr.decode("utf-8", "replace")
    except subprocess.TimeoutExpired:
        rc, out, err = "timeout", "", ""
    except OSError as e:
        rc, out, err = "oserror", "", str(e)
    return {"rc": rc, "stdout": scrub(out), "stderr": scrub(err)}


def write(cwd, name, text):
    path = os.path.join(cwd, name)
    with open(path, "w", encoding="utf-8") as f:
        f.write(text.lstrip("\n"))
    return path


def read(cwd, name):
    try:
        with open(os.path.join(cwd, name), encoding="utf-8", errors="replace") as f:
            return scrub(f.read())
    except OSError:
        return None


def mir_fn(mir_text, fn):
    """Return the MIR text of one function from an `--emit=mir` dump."""
    if mir_text is None:
        return None
    m = re.search(r"^fn %s\(.*?^}\n" % re.escape(fn), mir_text, re.S | re.M)
    return m.group(0) if m else None


def mir_block(fn_text, block):
    if fn_text is None:
        return None
    m = re.search(r"^    %s: \{\n.*?^    \}\n" % re.escape(block), fn_text, re.S | re.M)
    return m.group(0) if m else None


def llvm_fn(ll_text, fn):
    """Return the attribute comment and body of one `define` from LLVM IR."""
    if ll_text is None:
        return None
    m = re.search(
        r"(?:^; Function Attrs:[^\n]*\n)?^define [^\n]*@%s\(.*?^}\n" % re.escape(fn),
        ll_text, re.S | re.M,
    )
    return m.group(0) if m else None


HOISTED_NE = re.compile(r"= Ne\(copy _\d+, copy ")


def asm_fn(asm_text, fn):
    """Return the assembly of one function, without directives and labels."""
    if asm_text is None:
        return None
    m = re.search(r"^%s:\n(.*?)^\s*\.size\s+%s," % (re.escape(fn), re.escape(fn)),
                  asm_text, re.S | re.M)
    if not m:
        return None
    lines = [ln.strip() for ln in m.group(1).splitlines()]
    return [ln for ln in lines if ln and not ln.startswith(".") and not ln.endswith(":")]


def asm_call_sites(asm_text, fn):
    """Number of direct call or jump instructions that target the function."""
    if asm_text is None:
        return None
    return len(re.findall(r"^\s*(?:call|jmp)[a-z]*\s+\*?%s(?:@PLT)?\s*$" % re.escape(fn),
                          asm_text, re.M))


def errors_only(stderr):
    """Diagnostics of level `error`, without the surrounding warnings."""
    keep = []
    for block in re.split(r"\n(?=(?:error|warning)[:\[])", stderr):
        if block.startswith("error"):
            keep.append(block.strip())
    return keep


def ub_line(stderr):
    m = re.search(r"^error: Undefined Behavior: [^\n]*", stderr, re.M)
    return m.group(0) if m else None


# --------------------------------------------------------------------------
# Probe sections
# --------------------------------------------------------------------------

def native(rustc, cwd, src, tag, flags, fn):
    """Compile to MIR + LLVM IR + assembly + executable, run the executable."""
    exe = "%s_%s" % (os.path.splitext(src)[0], tag)
    comp = run([rustc, "--edition", "2021", "-Z", "validate-mir"] + flags +
               ["--emit=mir,llvm-ir,asm,link", "-o", exe, src], cwd)
    rec = {
        "flags": flags,
        "rustc_rc": comp["rc"],
        "rustc_errors": errors_only(comp["stderr"]),
    }
    if comp["rc"] == 0:
        r = run([os.path.join(cwd, exe)], cwd, timeout=60)
        rec["run_rc"] = r["rc"]
        rec["run_stdout"] = r["stdout"]
        fn_mir = mir_fn(read(cwd, exe + ".mir"), fn)
        rec["mir_fn"] = fn_mir
        rec["mir_has_hoisted_ne"] = bool(fn_mir and HOISTED_NE.search(fn_mir))
        rec["llvm_ir_fn"] = llvm_fn(read(cwd, exe + ".ll"), fn)
        asm = read(cwd, exe + ".s")
        rec["asm_fn_instructions"] = asm_fn(asm, fn)
        rec["asm_direct_calls_to_fn"] = asm_call_sites(asm, fn)
    return rec


def miri_run(miri, sysroot, cwd, src, flags):
    cmd = [miri, "--sysroot", sysroot, "--edition", "2021", "-Z", "validate-mir"] + flags + [src]
    r = run(cmd, cwd, timeout=600)
    return {
        "flags": flags,
        "miri_rc": r["rc"],
        "miri_stdout": r["stdout"],
        "miri_ub": ub_line(r["stderr"]),
        "miri_errors": errors_only(r["stderr"]),
    }


def probe_eob(rustc, miri, sysroot, cwd):
    out = {}
    custom = [
        ("eob_never_initialized_local", "eob_never_init.rs", EOB_NEVER_INIT, "eob_silicon_miscompile"),
        ("eob_dead_local", "eob_dead_local.rs", EOB_DEAD_LOCAL, "eob_dead_local_ub"),
        ("eob_upstream_custom_mir", "eob_upstream_custom_mir.rs", EOB_UPSTREAM_CUSTOM_MIR, "foo"),
    ]
    native_cfgs = [
        ("mir_opt_0", ["-Z", "mir-opt-level=0", "-C", "opt-level=2"]),
        ("mir_opt_1", ["-Z", "mir-opt-level=1", "-C", "opt-level=2"]),
        ("mir_opt_2", ["-Z", "mir-opt-level=2", "-C", "opt-level=2"]),
        ("mir_opt_2_without_early_otherwise_branch",
         ["-Z", "mir-opt-level=2", "-C", "opt-level=2",
          "-Z", "mir-enable-passes=-EarlyOtherwiseBranch"]),
    ]
    miri_cfgs = [
        ("mir_opt_0", ["-Zmir-opt-level=0"]),
        ("mir_opt_1", ["-Zmir-opt-level=1"]),
        ("mir_opt_2", ["-Zmir-opt-level=2"]),
        # `-C opt-level=2` keeps StorageLive/StorageDead in the MIR that Miri
        # interprets (RemoveStorageMarkers only runs when LLVM lifetime
        # markers would not be emitted).
        ("mir_opt_2_storage_markers_kept", ["-Zmir-opt-level=2", "-C", "opt-level=2"]),
        ("mir_opt_2_without_early_otherwise_branch",
         ["-Zmir-opt-level=2", "-Zmir-enable-passes=-EarlyOtherwiseBranch"]),
    ]
    for key, src, text, fn in custom:
        write(cwd, src, text)
        rec = {"function": fn, "native": {}, "miri": {}}
        for tag, flags in native_cfgs:
            rec["native"][tag] = native(rustc, cwd, src, tag, flags, fn)
        if miri:
            for tag, flags in miri_cfgs:
                rec["miri"][tag] = miri_run(miri, sysroot, cwd, src, flags)
        out[key] = rec

    surface = [
        ("eob_surface_union", "eob_surface_union.rs", EOB_SURFACE_UNION, "foo"),
        ("eob_surface_deref", "eob_surface_deref.rs", EOB_SURFACE_DEREF, "foo"),
    ]
    surf_native = [
        ("opt_level_0", ["-C", "opt-level=0"]),
        ("opt_level_1", ["-C", "opt-level=1"]),
        ("opt_level_2", ["-C", "opt-level=2"]),
        ("opt_level_s", ["-C", "opt-level=s"]),
        ("opt_level_3", ["-C", "opt-level=3"]),
        ("opt_level_3_without_early_otherwise_branch",
         ["-C", "opt-level=3", "-Z", "mir-enable-passes=-EarlyOtherwiseBranch"]),
        # The MIR pipeline Miri sees at `-Zmir-opt-level=2`, with and without
        # Miri's default `-Zmir-preserve-ub`.
        ("opt_level_0_mir_opt_2", ["-C", "opt-level=0", "-Z", "mir-opt-level=2"]),
        ("opt_level_0_mir_opt_2_preserve_ub",
         ["-C", "opt-level=0", "-Z", "mir-opt-level=2", "-Z", "mir-preserve-ub"]),
    ]
    surf_miri = [
        ("mir_opt_0", ["-Zmir-opt-level=0"]),
        # Miri's default `-Zmir-preserve-ub` keeps statements in the child
        # blocks that make the EarlyOtherwiseBranch pattern not match.
        ("mir_opt_2_default_preserve_ub", ["-Zmir-opt-level=2"]),
        ("mir_opt_2_preserve_ub_off", ["-Zmir-opt-level=2", "-Zmir-preserve-ub=no"]),
        ("mir_opt_2_preserve_ub_off_without_early_otherwise_branch",
         ["-Zmir-opt-level=2", "-Zmir-preserve-ub=no",
          "-Zmir-enable-passes=-EarlyOtherwiseBranch"]),
    ]
    for key, src, text, fn in surface:
        write(cwd, src, text)
        rec = {"function": fn, "native": {}, "miri": {}}
        for tag, flags in surf_native:
            rec["native"][tag] = native(rustc, cwd, src, tag, flags, fn)
        if miri:
            for tag, flags in surf_miri:
                rec["miri"][tag] = miri_run(miri, sysroot, cwd, src, flags)
        out[key] = rec
    return out


def probe_sci(rustc, miri, sysroot, cwd):
    src = "sci.rs"
    write(cwd, src, SCI)
    cfgs = [
        ("pass_off", ["-Z", "mir-opt-level=0"]),
        ("pass_on", ["-Z", "mir-opt-level=0",
                     "-Z", "mir-enable-passes=+SimplifyComparisonIntegral"]),
    ]
    out = {"native": {}, "miri": {}}
    for tag, flags in cfgs:
        exe = "sci_" + tag
        comp = run([rustc, "--edition", "2021", "-Z", "validate-mir", "-C", "opt-level=2"] +
                   flags + ["--emit=mir,link", "-o", exe, src], cwd)
        rec = {"flags": flags, "rustc_rc": comp["rc"],
               "rustc_errors": errors_only(comp["stderr"])}
        if comp["rc"] == 0:
            r = run([os.path.join(cwd, exe)], cwd, timeout=60)
            rec["run_rc"] = r["rc"]
            rec["run_stdout"] = r["stdout"]
            mir = read(cwd, exe + ".mir")
            rec["mir"] = {}
            for fn in SCI_FNS:
                fn_mir = mir_fn(mir, fn)
                rec["mir"][fn] = {
                    "bb0": mir_block(fn_mir, "bb0"),
                    "bb1": mir_block(fn_mir, "bb1"),
                    "bb2": mir_block(fn_mir, "bb2"),
                }
        out["native"][tag] = rec
    if miri:
        for tag, flags in [
            ("pass_off", ["-Zmir-opt-level=0"]),
            ("pass_on", ["-Zmir-opt-level=0",
                         "-Zmir-enable-passes=+SimplifyComparisonIntegral"]),
            ("pass_on_storage_markers_kept",
             ["-Zmir-opt-level=0", "-Zmir-enable-passes=+SimplifyComparisonIntegral",
              "-C", "opt-level=2"]),
        ]:
            out["miri"][tag] = miri_run(miri, sysroot, cwd, src, flags)
    return out


CALL_LINE = re.compile(r"^\s*_0 = [^\n]*-> \[return: [^\n]*\];\s*$", re.M)


def probe_ffi(rustc, cwd):
    d = os.path.join(cwd, "ffi")
    os.makedirs(d, exist_ok=True)
    for name, text in FFI_UP.items():
        write(d, name + ".rs", text)
    write(d, "down.rs", FFI_DOWN)
    rows = []
    for up, up_panic, down_panic in FFI_MATRIX:
        for stale in ("libffi_up.rlib", "down_bin", "up.mir"):
            try:
                os.remove(os.path.join(d, stale))
            except OSError:
                pass
        upc = run([rustc, "--edition", "2021", "--crate-name", "ffi_up",
                   "-C", "panic=" + up_panic, "-W", "ffi_unwind_calls",
                   "--emit=mir,link", "-o", "libffi_up.rlib", up + ".rs"], d)
        # With several emit kinds rustc derives each output name from `-o`.
        mir = read(d, "libffi_up.mir")
        lint = re.findall(r"^warning: ([^\n]*(?:FFI-unwind|unwind)[^\n]*)$", upc["stderr"], re.M)
        row = {
            "upstream_crate": up,
            "upstream_panic": up_panic,
            "downstream_panic": down_panic,
            "upstream_rc": upc["rc"],
            "upstream_errors": errors_only(upc["stderr"]),
            "ffi_unwind_calls_lint": sorted(set(lint)),
            "upstream_call_terminators": sorted(set(
                m.group(0).strip() for m in CALL_LINE.finditer(mir or ""))),
            "upstream_terminate_abi_sites": len(re.findall(r"terminate\(abi\)", mir or "")),
        }
        if upc["rc"] == 0:
            dn = run([rustc, "--edition", "2021", "-C", "panic=" + down_panic,
                      "--extern", "ffi_up=libffi_up.rlib", "-o", "down_bin", "down.rs"], d)
            row["downstream_link_rc"] = dn["rc"]
            row["downstream_errors"] = errors_only(dn["stderr"])
            if dn["rc"] == 0:
                r = run([os.path.join(d, "down_bin")], d, timeout=60)
                row["run_rc"] = r["rc"]
                row["run_stdout"] = r["stdout"]
        rows.append(row)
    return rows


def probe_ffi_no_std(rustc, cwd):
    """The unwind-rlib-with-FFI-unwind-call into abort-binary pairing, without std."""
    d = os.path.join(cwd, "ffi_no_std")
    os.makedirs(d, exist_ok=True)
    write(d, "up.rs", FFI_NO_STD_UP)
    write(d, "down.rs", FFI_NO_STD_DOWN)
    upc = run([rustc, "--edition", "2021", "--crate-name", "ffi_up", "-C", "panic=unwind",
               "--emit=mir,link", "-o", "libffi_up.rlib", "up.rs"], d)
    row = {
        "upstream_panic": "unwind",
        "downstream_panic": "abort",
        "upstream_rc": upc["rc"],
        "upstream_errors": errors_only(upc["stderr"]),
        "upstream_call_terminators": sorted(set(
            m.group(0).strip() for m in CALL_LINE.finditer(read(d, "libffi_up.mir") or ""))),
    }
    if upc["rc"] == 0:
        dn = run([rustc, "--edition", "2021", "-C", "panic=abort",
                  "--extern", "ffi_up=libffi_up.rlib", "-C", "link-arg=-lc",
                  "--emit=mir,link", "-o", "down_bin", "down.rs"], d)
        row["downstream_link_rc"] = dn["rc"]
        row["downstream_errors"] = errors_only(dn["stderr"])
        row["downstream_call_terminators"] = sorted(set(
            m.group(0).strip()
            for m in re.finditer(r"^\s*_\d+ = entry\([^\n]*;\s*$", read(d, "down_bin.mir") or "", re.M)))
        if dn["rc"] == 0:
            r = run([os.path.join(d, "down_bin")], d, timeout=60)
            row["run_rc"] = r["rc"]
    return row


def summarize(doc):
    s = {}
    eob = doc.get("early_otherwise_branch", {})

    def nat(case, cfg, field):
        return eob.get(case, {}).get("native", {}).get(cfg, {}).get(field)

    def mi(case, cfg, field):
        return eob.get(case, {}).get("miri", {}).get(cfg, {}).get(field)

    for case in ("eob_never_initialized_local", "eob_dead_local", "eob_upstream_custom_mir"):
        s[case] = {
            "hoisted_at_mir_opt_2": nat(case, "mir_opt_2", "mir_has_hoisted_ne"),
            "native_stdout_mir_opt_0": nat(case, "mir_opt_0", "run_stdout"),
            "native_stdout_mir_opt_2": nat(case, "mir_opt_2", "run_stdout"),
            "native_stdout_mir_opt_2_without_pass":
                nat(case, "mir_opt_2_without_early_otherwise_branch", "run_stdout"),
            "native_output_changes_with_pass":
                nat(case, "mir_opt_2", "run_stdout") !=
                nat(case, "mir_opt_2_without_early_otherwise_branch", "run_stdout"),
            "miri_ub_mir_opt_0": mi(case, "mir_opt_0", "miri_ub"),
            "miri_ub_mir_opt_2": mi(case, "mir_opt_2", "miri_ub"),
            "miri_ub_mir_opt_2_storage_markers_kept":
                mi(case, "mir_opt_2_storage_markers_kept", "miri_ub"),
            "miri_ub_mir_opt_2_without_pass":
                mi(case, "mir_opt_2_without_early_otherwise_branch", "miri_ub"),
        }
    for case in ("eob_surface_union", "eob_surface_deref"):
        s[case] = {
            "hoisted_at_opt_level_3": nat(case, "opt_level_3", "mir_has_hoisted_ne"),
            "hoisted_at_opt_level_0_mir_opt_2":
                nat(case, "opt_level_0_mir_opt_2", "mir_has_hoisted_ne"),
            "hoisted_at_opt_level_0_mir_opt_2_preserve_ub":
                nat(case, "opt_level_0_mir_opt_2_preserve_ub", "mir_has_hoisted_ne"),
            "native_stdout_opt_level_0": nat(case, "opt_level_0", "run_stdout"),
            "native_stdout_opt_level_1": nat(case, "opt_level_1", "run_stdout"),
            "native_stdout_opt_level_2": nat(case, "opt_level_2", "run_stdout"),
            "native_stdout_opt_level_s": nat(case, "opt_level_s", "run_stdout"),
            "native_stdout_opt_level_3": nat(case, "opt_level_3", "run_stdout"),
            "native_run_rc_opt_level_3": nat(case, "opt_level_3", "run_rc"),
            "native_stdout_opt_level_3_without_pass":
                nat(case, "opt_level_3_without_early_otherwise_branch", "run_stdout"),
            "miri_ub_mir_opt_0": mi(case, "mir_opt_0", "miri_ub"),
            "miri_ub_mir_opt_2_default_preserve_ub":
                mi(case, "mir_opt_2_default_preserve_ub", "miri_ub"),
            "miri_ub_mir_opt_2_preserve_ub_off": mi(case, "mir_opt_2_preserve_ub_off", "miri_ub"),
            "miri_ub_mir_opt_2_preserve_ub_off_without_pass":
                mi(case, "mir_opt_2_preserve_ub_off_without_early_otherwise_branch", "miri_ub"),
        }
    s["ffi_link_matrix"] = [
        {
            "upstream_crate": r["upstream_crate"],
            "upstream_panic": r["upstream_panic"],
            "downstream_panic": r["downstream_panic"],
            "links": r.get("downstream_link_rc") == 0,
            "error": (r.get("downstream_errors") or [None])[0],
        }
        for r in doc.get("ffi_unwind_link_matrix", [])
    ]
    ns = doc.get("ffi_unwind_no_std_link", {})
    s["ffi_no_std_unwind_rlib_with_ffi_unwind_call_into_abort_binary_links"] = \
        ns.get("downstream_link_rc") == 0
    return s


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--rustc", required=True, help="nightly rustc binary")
    ap.add_argument("--miri", help="miri driver binary of the same toolchain")
    ap.add_argument("--miri-sysroot", help="sysroot built by `cargo miri setup`")
    ap.add_argument("--out", help="write the JSON document here instead of stdout")
    args = ap.parse_args()
    if args.miri and not args.miri_sysroot:
        ap.error("--miri requires --miri-sysroot")

    rustc = os.path.abspath(os.path.expanduser(args.rustc))
    miri = os.path.abspath(os.path.expanduser(args.miri)) if args.miri else None
    sysroot = os.path.abspath(os.path.expanduser(args.miri_sysroot)) if args.miri else None

    with tempfile.TemporaryDirectory(prefix="eob_probe_") as cwd:
        # Keep machine-local paths out of the recorded output.
        SCRUB.append((cwd, "<tmp>"))
        if sysroot:
            SCRUB.append((sysroot, "<miri-sysroot>"))
        SCRUB.append((os.path.dirname(os.path.dirname(rustc)), "<toolchain>"))
        SCRUB.append((os.path.expanduser("~"), "<home>"))

        doc = {
            "rustc_version": run([rustc, "-Vv"], cwd)["stdout"].strip(),
            "miri_version": run([miri, "--version"], cwd)["stdout"].strip() if miri else None,
            "host_machine": os.uname().machine,
            "host_sysname": os.uname().sysname,
        }
        doc["early_otherwise_branch"] = probe_eob(rustc, miri, sysroot, cwd)
        doc["simplify_comparison_integral"] = probe_sci(rustc, miri, sysroot, cwd)
        doc["ffi_unwind_link_matrix"] = probe_ffi(rustc, cwd)
        doc["ffi_unwind_no_std_link"] = probe_ffi_no_std(rustc, cwd)
        doc["summary"] = summarize(doc)

    text = json.dumps(doc, indent=2, sort_keys=True) + "\n"
    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            f.write(text)
    else:
        sys.stdout.write(text)


if __name__ == "__main__":
    main()
