#!/usr/bin/env python3
"""Empirical probe for open-world Rust vtable deduplication, LLVM PGO/ICP symbol
fragility across CGU/LTO boundaries, Miri Tree Borrows safety, and runtime guard behavior.

Executes real upstream toolchains installed on the host (`rustc`, `llvm-profdata`,
`llvm-nm`, `miri -Zmiri-tree-borrows`, and native ELF/`dlopen` binaries) inside
self-cleaning `tempfile.TemporaryDirectory()` sandboxes with zero hardcoded metrics.
"""

from __future__ import annotations

import json
import os
import pathlib
import platform
import re
import statistics
import subprocess
import sys
import tempfile
import time
from typing import Any


def find_toolchains() -> dict[str, str]:
    home = pathlib.Path.home()
    env_path = os.environ.get("PATH", "")
    extra_dirs = [
        str(home / ".cargo" / "bin"),
        str(home / ".elan" / "bin"),
        str(home / ".local" / "bin"),
    ]
    search_path = os.pathsep.join(extra_dirs + [env_path])

    def which_req(binary: str) -> str:
        for d in search_path.split(os.pathsep):
            cand = pathlib.Path(d) / binary
            if cand.is_file() and os.access(cand, os.X_OK):
                return str(cand)
        raise RuntimeError(f"Required binary {binary!r} not found in {search_path}")

    rustc = which_req("rustc")
    sysroot = subprocess.check_output([rustc, "--print", "sysroot"], text=True).strip()
    host_line = [
        ln for ln in subprocess.check_output([rustc, "-vV"], text=True).splitlines()
        if ln.startswith("host:")
    ][0]
    host_triple = host_line.split(":", 1)[1].strip()
    rustlib_bin = pathlib.Path(sysroot) / "lib" / "rustlib" / host_triple / "bin"

    llvm_profdata = str(rustlib_bin / "llvm-profdata")
    llvm_nm = str(rustlib_bin / "llvm-nm")
    rust_lld = str(rustlib_bin / "rust-lld")
    miri_bin = pathlib.Path(sysroot) / "bin" / "miri"

    return {
        "rustc": rustc,
        "sysroot": sysroot,
        "host_triple": host_triple,
        "rustlib_bin": str(rustlib_bin),
        "llvm_profdata": llvm_profdata,
        "llvm_nm": llvm_nm,
        "rust_lld": rust_lld,
        "miri": str(miri_bin) if miri_bin.is_file() else "",
        "search_path": os.pathsep.join([str(rustlib_bin)] + extra_dirs + [env_path]),
    }


def run_cmd(
    args: list[str],
    *,
    cwd: pathlib.Path | None = None,
    env_extra: dict[str, str] | None = None,
    search_path: str | None = None,
    check: bool = True,
    timeout: int = 120,
) -> subprocess.CompletedProcess[str]:
    env = os.environ.copy()
    if search_path:
        env["PATH"] = search_path
    if env_extra:
        env.update(env_extra)
    t0 = time.perf_counter()
    proc = subprocess.run(
        args,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        timeout=timeout,
    )
    elapsed_ms = (time.perf_counter() - t0) * 1000.0
    proc.elapsed_ms = elapsed_ms  # type: ignore[attr-defined]
    if check and proc.returncode != 0:
        raise RuntimeError(
            f"Command failed (exit {proc.returncode}): {' '.join(args)}\n"
            f"STDOUT:\n{proc.stdout}\nSTDERR:\n{proc.stderr}"
        )
    return proc


# ---------------------------------------------------------------------------
# Experiment 1: Vtable & Generic Method Deduplication Matrix + dlopen DSO Probe
# ---------------------------------------------------------------------------

COMMON_TYPES_RS = r"""
#![crate_name = "common_types"]
#![crate_type = "rlib"]

pub trait TelemetryOp {
    fn sample(&self, x: u64) -> u64;
}

#[repr(C)]
pub struct SensorAlpha {
    pub bias: u64,
}

#[repr(C)]
pub struct SensorBeta {
    pub scale: u64,
    pub extra_word: u64,
}

#[repr(C)]
pub struct GenericSensor<T> {
    pub seed: T,
}

impl TelemetryOp for SensorAlpha {
    #[inline(never)]
    fn sample(&self, x: u64) -> u64 {
        if x == u64::MAX {
            panic!("deliberate_unwind_sensor_alpha");
        }
        x.wrapping_mul(3).wrapping_add(self.bias)
    }
}

impl TelemetryOp for SensorBeta {
    #[inline(never)]
    fn sample(&self, x: u64) -> u64 {
        x.wrapping_mul(self.scale).wrapping_add(self.extra_word)
    }
}

impl TelemetryOp for GenericSensor<u64> {
    #[inline(never)]
    fn sample(&self, x: u64) -> u64 {
        x.wrapping_add(self.seed ^ 0x55aa_55aa_55aa_55aa)
    }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct FatPtrRepr {
    pub data: usize,
    pub vtable: usize,
}

#[inline(never)]
pub fn inspect_dyn(op: &dyn TelemetryOp) -> (usize, usize) {
    // Rust trait object references `&(dyn Trait)` have layout `(data_ptr, vtable_ptr)`
    // where vtable layout is `[drop_in_place, size, align, method_0, ...]`
    // (`compiler/rustc_middle/src/ty/vtable.rs:45-52`).
    let repr: FatPtrRepr = unsafe { core::mem::transmute(op) };
    let method_slot0: usize = unsafe { *((repr.vtable as *const usize).add(3)) };
    (repr.vtable, method_slot0)
}
"""

SINGLE_CRATE_2MOD_RS = r"""
pub trait TelemetryOp {
    fn sample(&self, x: u64) -> u64;
}

#[repr(C)]
pub struct SensorAlpha {
    pub bias: u64,
}

#[repr(C)]
pub struct GenericSensor<T> {
    pub seed: T,
}

impl TelemetryOp for SensorAlpha {
    #[inline(never)]
    fn sample(&self, x: u64) -> u64 {
        x.wrapping_mul(3).wrapping_add(self.bias)
    }
}

impl<T: Copy + Into<u64>> TelemetryOp for GenericSensor<T> {
    #[inline(never)]
    fn sample(&self, x: u64) -> u64 {
        x.wrapping_add(self.seed.into() ^ 0x55aa)
    }
}

#[repr(C)]
#[derive(Copy, Clone)]
pub struct FatPtrRepr {
    pub data: usize,
    pub vtable: usize,
}

#[inline(never)]
pub fn inspect_dyn(op: &dyn TelemetryOp) -> (usize, usize) {
    let repr: FatPtrRepr = unsafe { core::mem::transmute(op) };
    let method_slot0: usize = unsafe { *((repr.vtable as *const usize).add(3)) };
    (repr.vtable, method_slot0)
}

pub mod unit_a {
    use super::{GenericSensor, SensorAlpha, TelemetryOp, inspect_dyn};
    static ALPHA_A: SensorAlpha = SensorAlpha { bias: 7 };
    static GEN_A: GenericSensor<u64> = GenericSensor { seed: 11 };

    #[inline(never)]
    pub fn get_alpha_addrs() -> (usize, usize) {
        let r: &dyn TelemetryOp = std::hint::black_box(&ALPHA_A);
        inspect_dyn(r)
    }

    #[inline(never)]
    pub fn get_generic_addrs() -> (usize, usize) {
        let r: &dyn TelemetryOp = std::hint::black_box(&GEN_A);
        inspect_dyn(r)
    }

    #[inline(never)]
    pub fn pad_work_a(mut v: u64) -> u64 {
        for i in 0..16u64 {
            v = v.rotate_left(5).wrapping_add(i ^ 0x9e37);
        }
        v
    }
}

pub mod unit_b {
    use super::{GenericSensor, SensorAlpha, TelemetryOp, inspect_dyn};
    static ALPHA_B: SensorAlpha = SensorAlpha { bias: 7 };
    static GEN_B: GenericSensor<u64> = GenericSensor { seed: 11 };

    #[inline(never)]
    pub fn get_alpha_addrs() -> (usize, usize) {
        let r: &dyn TelemetryOp = std::hint::black_box(&ALPHA_B);
        inspect_dyn(r)
    }

    #[inline(never)]
    pub fn get_generic_addrs() -> (usize, usize) {
        let r: &dyn TelemetryOp = std::hint::black_box(&GEN_B);
        inspect_dyn(r)
    }

    #[inline(never)]
    pub fn pad_work_b(mut v: u64) -> u64 {
        for i in 0..16u64 {
            v = v.rotate_right(3).wrapping_mul(i | 1);
        }
        v
    }
}

fn main() {
    let (vt_a, fn_a) = unit_a::get_alpha_addrs();
    let (vt_b, fn_b) = unit_b::get_alpha_addrs();
    let (gvt_a, gfn_a) = unit_a::get_generic_addrs();
    let (gvt_b, gfn_b) = unit_b::get_generic_addrs();
    let _keep = std::hint::black_box(unit_a::pad_work_a(1) ^ unit_b::pad_work_b(2));
    println!(
        "{{\"alpha_vt_a\":\"0x{:x}\",\"alpha_vt_b\":\"0x{:x}\",\"alpha_vt_eq\":{},\"alpha_fn_a\":\"0x{:x}\",\"alpha_fn_b\":\"0x{:x}\",\"alpha_fn_eq\":{},\"gen_vt_a\":\"0x{:x}\",\"gen_vt_b\":\"0x{:x}\",\"gen_vt_eq\":{},\"gen_fn_a\":\"0x{:x}\",\"gen_fn_b\":\"0x{:x}\",\"gen_fn_eq\":{}}}",
        vt_a, vt_b, if vt_a == vt_b { "true" } else { "false" },
        fn_a, fn_b, if fn_a == fn_b { "true" } else { "false" },
        gvt_a, gvt_b, if gvt_a == gvt_b { "true" } else { "false" },
        gfn_a, gfn_b, if gfn_a == gfn_b { "true" } else { "false" },
    );
}
"""

PROVIDER_TEMPLATE_RS = r"""
#![crate_name = "{crate_name}"]
#![crate_type = "rlib"]
extern crate common_types;
use common_types::{{GenericSensor, SensorAlpha, TelemetryOp, inspect_dyn}};

static ALPHA: SensorAlpha = SensorAlpha {{ bias: 7 }};
static GEN: GenericSensor<u64> = GenericSensor {{ seed: 11 }};

#[inline(never)]
pub fn alpha_dyn() -> &'static dyn TelemetryOp {{
    std::hint::black_box(&ALPHA)
}}

#[inline(never)]
pub fn generic_dyn() -> &'static dyn TelemetryOp {{
    std::hint::black_box(&GEN)
}}

#[inline(never)]
pub fn report_addrs() -> ((usize, usize), (usize, usize)) {{
    (inspect_dyn(alpha_dyn()), inspect_dyn(generic_dyn()))
}}
"""

TWO_RLIB_MAIN_RS = r"""
extern crate common_types;
extern crate provider_a;
extern crate provider_b;

fn main() {
    let ((vt_a, fn_a), (gvt_a, gfn_a)) = provider_a::report_addrs();
    let ((vt_b, fn_b), (gvt_b, gfn_b)) = provider_b::report_addrs();
    println!(
        "{{\"alpha_vt_a\":\"0x{:x}\",\"alpha_vt_b\":\"0x{:x}\",\"alpha_vt_eq\":{},\"alpha_fn_a\":\"0x{:x}\",\"alpha_fn_b\":\"0x{:x}\",\"alpha_fn_eq\":{},\"gen_vt_a\":\"0x{:x}\",\"gen_vt_b\":\"0x{:x}\",\"gen_vt_eq\":{},\"gen_fn_a\":\"0x{:x}\",\"gen_fn_b\":\"0x{:x}\",\"gen_fn_eq\":{}}}",
        vt_a, vt_b, if vt_a == vt_b { "true" } else { "false" },
        fn_a, fn_b, if fn_a == fn_b { "true" } else { "false" },
        gvt_a, gvt_b, if gvt_a == gvt_b { "true" } else { "false" },
        gfn_a, gfn_b, if gfn_a == gfn_b { "true" } else { "false" },
    );
}
"""

PLUGIN_CDYLIB_RS = r"""
#![crate_name = "plugin_b"]
#![crate_type = "cdylib"]
extern crate common_types;
use common_types::{FatPtrRepr, GenericSensor, SensorAlpha, TelemetryOp};

static PLUGIN_ALPHA: SensorAlpha = SensorAlpha { bias: 7 };
static PLUGIN_GEN: GenericSensor<u64> = GenericSensor { seed: 11 };

#[unsafe(no_mangle)]
pub extern "C" fn plugin_get_alpha_fatptr() -> FatPtrRepr {
    let r: &dyn TelemetryOp = std::hint::black_box(&PLUGIN_ALPHA);
    unsafe { core::mem::transmute(r) }
}

#[unsafe(no_mangle)]
pub extern "C" fn plugin_get_generic_fatptr() -> FatPtrRepr {
    let r: &dyn TelemetryOp = std::hint::black_box(&PLUGIN_GEN);
    unsafe { core::mem::transmute(r) }
}
"""

DLOPEN_HOST_RS = r"""
extern crate common_types;
use common_types::{FatPtrRepr, GenericSensor, SensorAlpha, SensorBeta, TelemetryOp, inspect_dyn};
use std::ffi::{CString, c_char, c_int, c_void};

unsafe extern "C" {
    fn dlopen(filename: *const c_char, flags: c_int) -> *mut c_void;
    fn dlsym(handle: *mut c_void, symbol: *const c_char) -> *mut c_void;
    fn dlclose(handle: *mut c_void) -> c_int;
}

const RTLD_NOW: c_int = 2;
const RTLD_LOCAL: c_int = 0;

static HOST_ALPHA: SensorAlpha = SensorAlpha { bias: 7 };
static HOST_BETA: SensorBeta = SensorBeta { scale: 100, extra_word: 999_999 };
static HOST_GEN: GenericSensor<u64> = GenericSensor { seed: 11 };

// Sound open-world value-guarded ICP:
// `if vptr == known_alpha_vptr { SensorAlpha::sample(data as &SensorAlpha, x) } else { op.sample(x) }`
#[inline(never)]
fn dispatch_value_guarded_icp(op: &dyn TelemetryOp, known_alpha_vptr: usize, x: u64) -> u64 {
    let repr: FatPtrRepr = unsafe { core::mem::transmute(op) };
    if repr.vtable == known_alpha_vptr {
        let concrete: &SensorAlpha = unsafe { &*(repr.data as *const SensorAlpha) };
        SensorAlpha::sample(concrete, x)
    } else {
        op.sample(x)
    }
}

// Unsound closed-world 2-impl peeled devirtualization:
// Assumes `{SensorAlpha, SensorBeta}` is exhaustive and unique-vtable, omitting the second guard!
// Note: `SensorBeta` is 16 bytes (`scale`, `extra_word`) while `SensorAlpha` is 8 bytes (`bias`).
// To avoid crashing the host process with SIGSEGV while demonstrating the exact type-confusion bug,
// we pass a padded buffer holding `SensorAlpha` followed by canary `0xdead_beef` so the out-of-bounds
// second field read by `SensorBeta::sample` is deterministically observable.
#[repr(C)]
struct PaddedAlpha {
    alpha: SensorAlpha,
    canary_adjacent_mem: u64,
}

#[inline(never)]
unsafe fn dispatch_unsound_closed_world_peeled(op: &dyn TelemetryOp, known_alpha_vptr: usize, x: u64) -> u64 {
    let repr: FatPtrRepr = unsafe { core::mem::transmute(op) };
    if repr.vtable == known_alpha_vptr {
        let concrete: &SensorAlpha = unsafe { &*(repr.data as *const SensorAlpha) };
        SensorAlpha::sample(concrete, x)
    } else {
        // BUG: Deduces `vptr != known_alpha_vptr => concrete type is SensorBeta`!
        let wrong: &SensorBeta = unsafe { &*(repr.data as *const SensorBeta) };
        SensorBeta::sample(wrong, x)
    }
}

fn main() {
    let so_path = std::env::args().nth(1).expect("expected path to libplugin_b.so");
    let c_path = CString::new(so_path).unwrap();
    let handle = unsafe { dlopen(c_path.as_ptr(), RTLD_NOW | RTLD_LOCAL) };
    assert!(!handle.is_null(), "dlopen failed");

    let sym_alpha = CString::new("plugin_get_alpha_fatptr").unwrap();
    let sym_gen = CString::new("plugin_get_generic_fatptr").unwrap();
    let get_alpha: extern "C" fn() -> FatPtrRepr =
        unsafe { core::mem::transmute(dlsym(handle, sym_alpha.as_ptr())) };
    let get_gen: extern "C" fn() -> FatPtrRepr =
        unsafe { core::mem::transmute(dlsym(handle, sym_gen.as_ptr())) };

    let host_alpha_dyn: &dyn TelemetryOp = std::hint::black_box(&HOST_ALPHA);
    let _host_beta_dyn: &dyn TelemetryOp = std::hint::black_box(&HOST_BETA);
    let host_gen_dyn: &dyn TelemetryOp = std::hint::black_box(&HOST_GEN);

    let (host_vt, host_fn) = inspect_dyn(host_alpha_dyn);
    let (host_gvt, host_gfn) = inspect_dyn(host_gen_dyn);

    let plugin_alpha_repr = get_alpha();
    let plugin_alpha_dyn: &dyn TelemetryOp = unsafe { core::mem::transmute(plugin_alpha_repr) };
    let (plugin_vt, plugin_fn) = inspect_dyn(plugin_alpha_dyn);

    let plugin_gen_repr = get_gen();
    let plugin_gen_dyn: &dyn TelemetryOp = unsafe { core::mem::transmute(plugin_gen_repr) };
    let (plugin_gvt, plugin_gfn) = inspect_dyn(plugin_gen_dyn);

    // Construct a padded SensorAlpha using the plugin's valid SensorAlpha vtable:
    let padded = PaddedAlpha {
        alpha: SensorAlpha { bias: 7 },
        canary_adjacent_mem: 0x00de_adbe_ef00_0001,
    };
    let plugin_backed_padded_repr = FatPtrRepr {
        data: (&padded.alpha as *const SensorAlpha) as usize,
        vtable: plugin_vt,
    };
    let plugin_backed_alpha: &dyn TelemetryOp =
        unsafe { core::mem::transmute(plugin_backed_padded_repr) };

    let expected = 10u64 * 3 + 7; // 37
    let guarded_host = dispatch_value_guarded_icp(host_alpha_dyn, host_vt, 10);
    let guarded_plugin = dispatch_value_guarded_icp(plugin_backed_alpha, host_vt, 10);
    let unsound_peeled_plugin =
        unsafe { dispatch_unsound_closed_world_peeled(plugin_backed_alpha, host_vt, 10) };

    let mode = std::env::args().nth(2).unwrap_or_default();
    if mode == "--test-plugin-unwind" {
        let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            dispatch_value_guarded_icp(plugin_backed_alpha, host_vt, u64::MAX)
        }))
        .is_err();
        println!("{{\"plugin_unwind_caught\":{}}}", if caught { "true" } else { "false" });
        unsafe { dlclose(handle); }
        return;
    }

    // Verify panic unwinding on fast path (host_vt -> host's libstd CANARY):
    let unwind_host = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        dispatch_value_guarded_icp(host_alpha_dyn, host_vt, u64::MAX)
    }))
    .is_err();

    println!(
        "{{\"alpha_vt_a\":\"0x{:x}\",\"alpha_vt_b\":\"0x{:x}\",\"alpha_vt_eq\":{},\"alpha_fn_a\":\"0x{:x}\",\"alpha_fn_b\":\"0x{:x}\",\"alpha_fn_eq\":{},\"gen_vt_a\":\"0x{:x}\",\"gen_vt_b\":\"0x{:x}\",\"gen_vt_eq\":{},\"gen_fn_a\":\"0x{:x}\",\"gen_fn_b\":\"0x{:x}\",\"gen_fn_eq\":{},\"expected_val\":{},\"guarded_host_val\":{},\"guarded_plugin_val\":{},\"unsound_peeled_plugin_val\":{},\"unwind_host_caught\":{}}}",
        host_vt, plugin_vt, if host_vt == plugin_vt { "true" } else { "false" },
        host_fn, plugin_fn, if host_fn == plugin_fn { "true" } else { "false" },
        host_gvt, plugin_gvt, if host_gvt == plugin_gvt { "true" } else { "false" },
        host_gfn, plugin_gfn, if host_gfn == plugin_gfn { "true" } else { "false" },
        expected, guarded_host, guarded_plugin, unsound_peeled_plugin,
        if unwind_host { "true" } else { "false" },
    );

    unsafe {
        dlclose(handle);
    }
}
"""


def count_vtable_globals_in_ll(ll_files: list[pathlib.Path]) -> dict[str, int]:
    private_unnamed = 0
    private_named_addr = 0
    type_test_calls = 0
    vcall_vis_md = 0
    for lf in ll_files:
        txt = lf.read_text(errors="replace")
        for line in txt.splitlines():
            if "vtable" in line and "constant <{" in line:
                if "unnamed_addr" in line:
                    private_unnamed += 1
                else:
                    private_named_addr += 1
            if "@llvm.type.test" in line:
                type_test_calls += 1
            if "!vcall_visibility" in line:
                vcall_vis_md += 1
    return {
        "vtable_defs_unnamed_addr": private_unnamed,
        "vtable_defs_no_unnamed_addr": private_named_addr,
        "llvm_type_test_occurrences": type_test_calls,
        "vcall_visibility_md_occurrences": vcall_vis_md,
    }


def run_experiment_1_vtable_matrix(tc: dict[str, str]) -> list[dict[str, Any]]:
    rustc = tc["rustc"]
    sp = tc["search_path"]
    results: list[dict[str, Any]] = []

    with tempfile.TemporaryDirectory(prefix="vtable_matrix_") as tmp:
        ws = pathlib.Path(tmp)
        single_src = ws / "single_2mod.rs"
        single_src.write_text(SINGLE_CRATE_2MOD_RS)

        single_configs = [
            ("single_cgu1_o2", ["-C", "opt-level=2", "-C", "codegen-units=1", "-C", "lto=off", "-C", "debuginfo=0"]),
            ("single_cgu2_o2", ["-C", "opt-level=2", "-C", "codegen-units=2", "-C", "lto=off", "-C", "debuginfo=0"]),
            (
                "single_cgu2_lld_icf_safe",
                [
                    "-C", "opt-level=2", "-C", "codegen-units=2", "-C", "lto=off", "-C", "debuginfo=0",
                    "-Z", "unstable-options", "-C", "linker-flavor=gnu-lld-cc", "-C", "link-arg=-Wl,--icf=safe",
                ],
            ),
            (
                "single_cgu2_lld_icf_all",
                [
                    "-C", "opt-level=2", "-C", "codegen-units=2", "-C", "lto=off", "-C", "debuginfo=0",
                    "-Z", "unstable-options", "-C", "linker-flavor=gnu-lld-cc", "-C", "link-arg=-Wl,--icf=all",
                ],
            ),
        ]

        for name, flags in single_configs:
            out_dir = ws / name
            out_dir.mkdir()
            bin_path = out_dir / "single_2mod"
            cproc = run_cmd(
                [rustc, str(single_src), "--crate-name", "single_2mod", "--emit=llvm-ir,link", "--out-dir", str(out_dir)] + flags,
                cwd=out_dir,
                search_path=sp,
            )
            rproc = run_cmd([str(bin_path)], cwd=out_dir, search_path=sp)
            obs = json.loads(rproc.stdout.strip())
            ll_files = sorted(out_dir.glob("*.ll"))
            ll_stats = count_vtable_globals_in_ll(ll_files)
            ll_stats["cgu_ll_file_count"] = len(ll_files)
            results.append({
                "config": name,
                "flags": flags,
                "compile_ms": round(cproc.elapsed_ms, 2),  # type: ignore[attr-defined]
                **obs,
                **ll_stats,
            })

        # Multi-rlib configurations
        common_src = ws / "common_types.rs"
        prov_a_src = ws / "provider_a.rs"
        prov_b_src = ws / "provider_b.rs"
        main_src = ws / "two_rlib_main.rs"
        common_src.write_text(COMMON_TYPES_RS)
        prov_a_src.write_text(PROVIDER_TEMPLATE_RS.format(crate_name="provider_a"))
        prov_b_src.write_text(PROVIDER_TEMPLATE_RS.format(crate_name="provider_b"))
        main_src.write_text(TWO_RLIB_MAIN_RS)

        rlib_configs = [
            ("two_rlibs_o2_default", ["-C", "opt-level=2", "-C", "codegen-units=1", "-C", "debuginfo=0"]),
            ("two_rlibs_o2_share_generics", ["-C", "opt-level=2", "-C", "codegen-units=1", "-C", "debuginfo=0", "-Z", "share-generics=yes"]),
            ("two_rlibs_fat_lto_debug0", ["-C", "opt-level=2", "-C", "codegen-units=1", "-C", "lto=fat", "-C", "debuginfo=0"]),
            ("two_rlibs_fat_lto_debug2", ["-C", "opt-level=2", "-C", "codegen-units=1", "-C", "lto=fat", "-C", "debuginfo=2"]),
        ]

        for name, flags in rlib_configs:
            out_dir = ws / name
            out_dir.mkdir()
            # Pre-link flags for rlibs (omit -C lto=fat on rlib itself; pass -C embed-bitcode=yes, then -C lto=fat on final link)
            rlib_flags = [f for f in flags if f != "lto=fat"]
            if "lto=fat" in flags:
                # remove dangling "-C" before "lto=fat"
                cleaned: list[str] = []
                skip = False
                for i, tok in enumerate(flags):
                    if skip:
                        skip = False
                        continue
                    if tok == "-C" and i + 1 < len(flags) and flags[i + 1] == "lto=fat":
                        skip = True
                        continue
                    cleaned.append(tok)
                rlib_flags = cleaned + ["-C", "embed-bitcode=yes"]
            else:
                rlib_flags = list(flags)

            t0 = time.perf_counter()
            run_cmd([rustc, str(common_src), "--out-dir", str(out_dir)] + rlib_flags, cwd=out_dir, search_path=sp)
            run_cmd([rustc, str(prov_a_src), "-L", str(out_dir), "--emit=llvm-ir,link", "--out-dir", str(out_dir)] + rlib_flags, cwd=out_dir, search_path=sp)
            run_cmd([rustc, str(prov_b_src), "-L", str(out_dir), "--emit=llvm-ir,link", "--out-dir", str(out_dir)] + rlib_flags, cwd=out_dir, search_path=sp)
            bin_path = out_dir / "two_rlib_main"
            run_cmd([rustc, str(main_src), "--crate-name", "two_rlib_main", "-L", str(out_dir), "--emit=llvm-ir,link", "--out-dir", str(out_dir)] + flags, cwd=out_dir, search_path=sp)
            compile_ms = (time.perf_counter() - t0) * 1000.0

            rproc = run_cmd([str(bin_path)], cwd=out_dir, search_path=sp)
            obs = json.loads(rproc.stdout.strip())
            ll_stats = count_vtable_globals_in_ll(sorted(out_dir.glob("*.ll")))
            results.append({
                "config": name,
                "flags": flags,
                "compile_ms": round(compile_ms, 2),
                **obs,
                **ll_stats,
            })

        # Config 9: dlopen cdylib (RTLD_LOCAL)
        dl_dir = ws / "dlopen_cdylib_o2"
        dl_dir.mkdir()
        plugin_src = ws / "plugin_b.rs"
        host_src = ws / "dlopen_host.rs"
        plugin_src.write_text(PLUGIN_CDYLIB_RS)
        host_src.write_text(DLOPEN_HOST_RS)

        t0 = time.perf_counter()
        run_cmd([rustc, str(common_src), "-C", "opt-level=2", "--out-dir", str(dl_dir)], cwd=dl_dir, search_path=sp)
        so_path = dl_dir / "libplugin_b.so"
        run_cmd([rustc, str(plugin_src), "-L", str(dl_dir), "-C", "opt-level=2", "-o", str(so_path)], cwd=dl_dir, search_path=sp)
        host_bin = dl_dir / "dlopen_host"
        run_cmd([rustc, str(host_src), "-L", str(dl_dir), "-C", "opt-level=2", "-C", "link-arg=-ldl", "-o", str(host_bin)], cwd=dl_dir, search_path=sp)
        dl_compile_ms = (time.perf_counter() - t0) * 1000.0

        rproc = run_cmd([str(host_bin), str(so_path)], cwd=dl_dir, search_path=sp)
        obs = json.loads(rproc.stdout.strip())
        uproc_cdylib = run_cmd([str(host_bin), str(so_path), "--test-plugin-unwind"], cwd=dl_dir, search_path=sp, check=False)
        obs["plugin_unwind_exit_code"] = uproc_cdylib.returncode
        obs["plugin_unwind_foreign_abort"] = ("Rust cannot catch foreign exceptions" in uproc_cdylib.stderr)
        results.append({
            "config": "dlopen_cdylib_rtld_local_o2",
            "flags": ["-C", "opt-level=2", "--crate-type=cdylib", "RTLD_LOCAL"],
            "compile_ms": round(dl_compile_ms, 2),
            **obs,
        })

        # Config 10: dlopen shared-std dylib (-C prefer-dynamic)
        dy_dir = ws / "dlopen_dylib_prefer_dynamic_o2"
        dy_dir.mkdir()
        common_dylib_src = ws / "common_types_dylib.rs"
        common_dylib_src.write_text(COMMON_TYPES_RS.replace('#![crate_type = "rlib"]', '#![crate_type = "dylib"]'))
        plugin_dylib_src = ws / "plugin_b_dylib.rs"
        plugin_dylib_src.write_text(PLUGIN_CDYLIB_RS.replace('#![crate_type = "cdylib"]', '#![crate_type = "dylib"]'))
        sysroot_lib = str(pathlib.Path(tc["sysroot"]) / "lib")
        rustlib_target_lib = str(pathlib.Path(tc["sysroot"]) / "lib" / "rustlib" / tc["host_triple"] / "lib")
        ld_env = {"LD_LIBRARY_PATH": f"{dy_dir}:{rustlib_target_lib}:{sysroot_lib}"}

        t0 = time.perf_counter()
        run_cmd([rustc, str(common_dylib_src), "-C", "prefer-dynamic", "-C", "opt-level=2", "--out-dir", str(dy_dir)], cwd=dy_dir, search_path=sp)
        dy_so = dy_dir / "libplugin_b.so"
        run_cmd([rustc, str(plugin_dylib_src), "-L", str(dy_dir), "-C", "prefer-dynamic", "-C", "opt-level=2", "-o", str(dy_so)], cwd=dy_dir, search_path=sp)
        dy_host = dy_dir / "dlopen_host_dylib"
        run_cmd([rustc, str(host_src), "-L", str(dy_dir), "-C", "prefer-dynamic", "-C", "opt-level=2", "-C", "link-arg=-ldl", "-o", str(dy_host)], cwd=dy_dir, search_path=sp)
        dy_compile_ms = (time.perf_counter() - t0) * 1000.0

        rproc_dy = run_cmd([str(dy_host), str(dy_so)], cwd=dy_dir, env_extra=ld_env, search_path=sp)
        obs_dy = json.loads(rproc_dy.stdout.strip())
        uproc_dy = run_cmd([str(dy_host), str(dy_so), "--test-plugin-unwind"], cwd=dy_dir, env_extra=ld_env, search_path=sp, check=False)
        obs_dy["plugin_unwind_exit_code"] = uproc_dy.returncode
        obs_dy["plugin_unwind_caught_cleanly"] = (uproc_dy.returncode == 0 and '"plugin_unwind_caught":true' in uproc_dy.stdout)
        results.append({
            "config": "dlopen_dylib_prefer_dynamic_o2",
            "flags": ["-C", "opt-level=2", "-C", "prefer-dynamic", "--crate-type=dylib", "RTLD_LOCAL"],
            "compile_ms": round(dy_compile_ms, 2),
            **obs_dy,
        })

    return results


# ---------------------------------------------------------------------------
# Experiment 2: Real LLVM IRPGO CGU/LTO Fragility vs. Canonical MIR Keys
# ---------------------------------------------------------------------------

PGO_PROBE_BASE_RS = r"""
pub trait StepOp {
    fn step(&self, acc: u64, x: u64) -> u64;
}

pub mod worker_local {
    use super::StepOp;

    pub struct HotLocalImpl {
        pub k: u64,
    }

    // Non-pub helper and impl method placed in worker_local's CGU under multi-CGU partitioning.
    #[inline(never)]
    fn private_mix(a: u64, b: u64) -> u64 {
        a.wrapping_mul(6364136223846793005).wrapping_add(b ^ 0x9e3779b97f4a7c15)
    }

    impl StepOp for HotLocalImpl {
        #[inline(never)]
        fn step(&self, acc: u64, x: u64) -> u64 {
            private_mix(acc ^ self.k, x)
        }
    }

    #[inline(never)]
    pub fn run_internal_fn_icall(iters: u64) -> u64 {
        let fp: fn(u64, u64) -> u64 = std::hint::black_box(private_mix);
        let mut acc = 1u64;
        for i in 0..iters {
            acc = fp(acc, i);
        }
        acc
    }

    #[inline(never)]
    pub fn bulk_padding_worker(mut v: u64) -> u64 {
        for i in 0..32u64 {
            v = v.rotate_left(7).wrapping_add(i.wrapping_mul(17));
        }
        v
    }
}

pub mod cold_exported {
    use super::StepOp;

    pub struct ColdExportImpl {
        pub c: u64,
    }

    impl StepOp for ColdExportImpl {
        #[inline(never)]
        fn step(&self, acc: u64, x: u64) -> u64 {
            acc.wrapping_sub(x).wrapping_add(self.c)
        }
    }

    #[inline(never)]
    pub fn bulk_padding_cold(mut v: u64) -> u64 {
        for i in 0..32u64 {
            v = v.rotate_right(11).wrapping_mul(i | 3);
        }
        v
    }
}

pub mod dispatcher {
    use super::StepOp;

    #[inline(never)]
    pub fn run_dyn_dispatch(ops: &[&dyn StepOp], rounds: u64) -> u64 {
        let mut acc = 0x1234_5678u64;
        for r in 0..rounds {
            for op in ops {
                acc = op.step(acc, r);
            }
        }
        acc
    }
}

{extra_module}

fn main() {
    let hot = worker_local::HotLocalImpl { k: 42 };
    let cold = cold_exported::ColdExportImpl { c: 9 };
    let h_ref: &dyn StepOp = std::hint::black_box(&hot);
    let c_ref: &dyn StepOp = std::hint::black_box(&cold);
    // 95% hot, 5% cold across 20 slots * 2000 rounds = 40,000 indirect calls
    let table: [&dyn StepOp; 20] = [
        h_ref, h_ref, h_ref, h_ref, h_ref,
        h_ref, h_ref, h_ref, h_ref, h_ref,
        h_ref, h_ref, h_ref, h_ref, h_ref,
        h_ref, h_ref, h_ref, h_ref, c_ref,
    ];
    let d_res = dispatcher::run_dyn_dispatch(&table, 2000);
    let f_res = worker_local::run_internal_fn_icall(40000);
    let pad = worker_local::bulk_padding_worker(1) ^ cold_exported::bulk_padding_cold(2);
    std::hint::black_box(d_res ^ f_res ^ pad);
}
"""

EXTRA_PERTURBATION_MOD = r"""
pub mod extra_unrelated_module {
    #[inline(never)]
    pub fn unrelated_work(mut x: u64) -> u64 {
        for i in 0..64u64 {
            x = x.wrapping_mul(0xbf58476d1ce4e5b9).wrapping_add(i);
        }
        x
    }
}
"""


def extract_canonical_mir_keys(mir_path: pathlib.Path) -> dict[str, list[str]]:
    """Extract canonical `(DefPath -> ordered callsite callee signatures)` from `--emit=mir`.

    Strips unstable local variable numbering noise while preserving exact item DefPaths
    and terminator call targets in source-block order.
    """
    txt = mir_path.read_text(errors="replace")
    fn_header_re = re.compile(r"^fn\s+([A-Za-z0-9_<>:,\s'&]+?)\s*\(", re.MULTILINE)
    # Split by top-level `fn <path>(` headers
    matches = list(fn_header_re.finditer(txt))
    keys: dict[str, list[str]] = {}
    for idx, m in enumerate(matches):
        def_path = " ".join(m.group(1).strip().split())
        if "extra_unrelated_module" in def_path or "unrelated_work" in def_path:
            continue
        start = m.start()
        end = matches[idx + 1].start() if idx + 1 < len(matches) else len(txt)
        body = txt[start:end]
        call_targets: list[str] = []
        for line in body.splitlines():
            s = line.strip()
            # Match MIR call terminators: `_X = <callee>(...) -> [return: ...`
            if " -> [" in s and "=" in s and "(" in s:
                rhs = s.split("=", 1)[1].strip()
                callee = rhs.split("(", 1)[0].strip()
                # Normalize MIR local names (`move _3` -> `move _LOCAL`) for indirect calls
                callee_norm = re.sub(r"\b_\d+\b", "_LOCAL", callee)
                call_targets.append(callee_norm)
        keys[def_path] = call_targets
    return dict(sorted(keys.items()))


def run_experiment_2_pgo_vs_mir(tc: dict[str, str]) -> dict[str, Any]:
    rustc = tc["rustc"]
    profdata_bin = tc["llvm_profdata"]
    sp = tc["search_path"]

    with tempfile.TemporaryDirectory(prefix="pgo_cgu_mir_") as tmp:
        ws = pathlib.Path(tmp)
        base_src = ws / "pgo_app.rs"
        pert_src = ws / "pgo_app_perturbed.rs"
        base_src.write_text(PGO_PROBE_BASE_RS.replace("{extra_module}", ""))
        pert_src.write_text(PGO_PROBE_BASE_RS.replace("{extra_module}", EXTRA_PERTURBATION_MOD))

        profraw_dir = ws / "profraw"
        profraw_dir.mkdir()
        gen_bin = ws / "pgo_gen_bin"

        # 1. Build instrumented binary with -C codegen-units=4 -C lto=off
        run_cmd(
            [
                rustc, str(base_src),
                "--crate-name", "pgo_app",
                "-C", "opt-level=2",
                "-C", "codegen-units=4",
                "-C", "lto=off",
                f"-Cprofile-generate={profraw_dir}",
                "-o", str(gen_bin),
            ],
            cwd=ws,
            search_path=sp,
        )

        # 2. Execute training run to emit .profraw
        run_cmd([str(gen_bin)], cwd=ws, search_path=sp)
        profraws = sorted(profraw_dir.glob("*.profraw"))
        if not profraws:
            raise RuntimeError("No .profraw generated by -C profile-generate binary")

        profdata_path = ws / "merged.profdata"
        run_cmd(
            [profdata_bin, "merge", "-o", str(profdata_path)] + [str(p) for p in profraws],
            cwd=ws,
            search_path=sp,
        )

        show_proc = run_cmd(
            [profdata_bin, "show", "--all-functions", "--ic-targets", str(profdata_path)],
            cwd=ws,
            search_path=sp,
        )

        # Parse CGU-prefixed internal symbol names vs external symbol names in .profdata
        cgu_prefixed_symbols: list[str] = []
        unprefixed_symbols: list[str] = []
        icp_target_records: list[str] = []
        lines = show_proc.stdout.splitlines()
        for i, ln in enumerate(lines):
            if ln.startswith("  ") and ln.endswith(":") and not ln.strip().startswith("Hash:") and not ln.strip().startswith("Counters:"):
                sym = ln.strip()[:-1]
                if "-cgu." in sym and (";" in sym or ":" in sym):
                    cgu_prefixed_symbols.append(sym)
                else:
                    unprefixed_symbols.append(sym)
            if "Indirect Target Results:" in ln:
                for sub in lines[i + 1 : i + 6]:
                    if sub.strip().startswith("["):
                        icp_target_records.append(sub.strip())
                    else:
                        break

        # 3. Replay -C profile-use across 5 compilation topologies with ICP remarks
        replay_modes = [
            ("cgu4_lto_off_match", base_src, ["-C", "opt-level=2", "-C", "codegen-units=4", "-C", "lto=off"]),
            ("cgu1_lto_off_switch", base_src, ["-C", "opt-level=2", "-C", "codegen-units=1", "-C", "lto=off"]),
            ("cgu4_thin_lto_switch", base_src, ["-C", "opt-level=2", "-C", "codegen-units=4", "-C", "lto=thin"]),
            ("cgu4_fat_lto_switch", base_src, ["-C", "opt-level=2", "-C", "codegen-units=4", "-C", "lto=fat"]),
            ("cgu3_perturbed_switch", pert_src, ["-C", "opt-level=2", "-C", "codegen-units=3", "-C", "lto=off"]),
        ]

        baseline_mir_keys: dict[str, list[str]] | None = None
        replay_results: list[dict[str, Any]] = []

        for mode_name, src_file, mode_flags in replay_modes:
            mdir = ws / mode_name
            mdir.mkdir()
            out_bin = mdir / "pgo_app"
            uproc = run_cmd(
                [
                    rustc, str(src_file),
                    "--crate-name", "pgo_app",
                    f"-Cprofile-use={profdata_path}",
                    "-C", "llvm-args=-pass-remarks=pgo-icall-prom",
                    "-C", "llvm-args=-pass-remarks-missed=pgo-icall-prom",
                    "--emit=mir,llvm-ir,link",
                    "--out-dir", str(mdir),
                ]
                + mode_flags,
                cwd=mdir,
                search_path=sp,
            )

            stderr = uproc.stderr
            promoted_remarks = [
                ln.strip() for ln in stderr.splitlines()
                if "remark:" in ln and "Promote indirect call" in ln
            ]
            missed_remarks = [
                ln.strip() for ln in stderr.splitlines()
                if "remark:" in ln and ("Cannot promote indirect call" in ln or "Do not promote indirect call" in ln)
            ]
            pgo_warnings = [
                ln.strip() for ln in stderr.splitlines()
                if "profile data" in ln.lower() or "mismatched" in ln.lower() or "inconsistent" in ln.lower()
            ]

            # Inspect emitted LLVM IR for ICP blocks (`if.true.direct_targ`) and guard instruction kind
            icp_blocks = 0
            func_cmp_guards = 0
            vtable_cmp_guards = 0
            for llf in sorted(mdir.glob("*.ll")):
                ll_txt = llf.read_text(errors="replace")
                icp_blocks += ll_txt.count("if.true.direct_targ:")
                for m_blk in re.finditer(r"icmp eq ptr ([^\n]+)\n\s*br i1 %[^\n]+label %if\.true\.direct_targ", ll_txt):
                    cmp_rhs = m_blk.group(1)
                    if "vtable" in cmp_rhs:
                        vtable_cmp_guards += 1
                    else:
                        func_cmp_guards += 1

            mir_files = sorted(mdir.glob("*.mir"))
            mir_keys = extract_canonical_mir_keys(mir_files[0])
            if baseline_mir_keys is None:
                baseline_mir_keys = mir_keys
            mir_keys_identical = (mir_keys == baseline_mir_keys)

            replay_results.append({
                "mode": mode_name,
                "flags": mode_flags,
                "compile_ms": round(uproc.elapsed_ms, 2),  # type: ignore[attr-defined]
                "promoted_count": len(promoted_remarks),
                "missed_count": len(missed_remarks),
                "promoted_remarks": promoted_remarks,
                "missed_remarks": missed_remarks,
                "pgo_warnings": pgo_warnings,
                "llvm_ir_icp_direct_blocks": icp_blocks,
                "llvm_ir_func_ptr_guards": func_cmp_guards,
                "llvm_ir_vtable_ptr_guards": vtable_cmp_guards,
                "canonical_mir_item_count": len(mir_keys),
                "canonical_mir_keys_match_baseline": mir_keys_identical,
            })

    return {
        "profdata_cgu_prefixed_symbol_count": len(cgu_prefixed_symbols),
        "profdata_unprefixed_symbol_count": len(unprefixed_symbols),
        "profdata_cgu_prefixed_examples": cgu_prefixed_symbols[:6],
        "profdata_unprefixed_examples": unprefixed_symbols[:6],
        "profdata_icp_target_records": icp_target_records,
        "canonical_mir_keys_snapshot": baseline_mir_keys or {},
        "replay_modes": replay_results,
    }


# ---------------------------------------------------------------------------
# Experiment 3: Zero-Sysroot `#![no_core]` Miri `-Zmiri-tree-borrows` Litmus Suite
# ---------------------------------------------------------------------------

MIRI_NOCORE_PRELUDE = r"""
#![feature(no_core, lang_items, rustc_attrs, auto_traits, negative_impls, freeze_impls, intrinsics)]
#![no_core]
#![allow(internal_features)]

#[lang = "pointee_sized"] pub trait PointeeSized {}
#[lang = "meta_sized"] pub trait MetaSized: PointeeSized {}
#[lang = "sized"] pub trait Sized: MetaSized {}
#[lang = "copy"] pub trait Copy {}
#[lang = "freeze"] pub unsafe auto trait Freeze {}
#[lang = "unpin"] pub auto trait Unpin {}
#[lang = "unsafe_unpin"] pub unsafe auto trait UnsafeUnpin {}
#[lang = "unsafe_cell"] #[repr(transparent)] pub struct UnsafeCell<T: ?Sized> { pub value: T }
impl<T: ?Sized> !Freeze for UnsafeCell<T> {}
impl<T> UnsafeCell<T> {
    #[allow(invalid_reference_casting)]
    pub fn get(&self) -> *mut T {
        self as *const UnsafeCell<T> as *const T as *mut T
    }
}
#[lang = "unsize"] pub trait Unsize<T: ?Sized> {}
#[lang = "coerce_unsized"] pub trait CoerceUnsized<T> {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<&'a U> for &'a T {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<&'a mut U> for &'a mut T {}
#[lang = "dispatch_from_dyn"] pub trait DispatchFromDyn<T> {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<&'a U> for &'a T {}
impl<'a, T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<&'a mut U> for &'a mut T {}
#[lang = "legacy_receiver"] pub trait LegacyReceiver {}
impl<T: ?Sized> LegacyReceiver for &T {}
impl<T: ?Sized> LegacyReceiver for &mut T {}
#[lang = "drop_glue"]
pub unsafe fn drop_in_place<T: ?Sized>(_to_drop: *mut T) {}

impl Copy for usize {}
impl Copy for isize {}
impl Copy for bool {}
impl<T: ?Sized> Copy for *const T {}
impl<T: ?Sized> Copy for *mut T {}
impl<T: ?Sized> Copy for &T {}
impl Copy for [usize; 4] {}

#[rustc_intrinsic]
unsafe fn transmute<Src, Dst>(src: Src) -> Dst;
#[rustc_intrinsic]
fn wrapping_add<T: Copy>(a: T, b: T) -> T;
#[rustc_intrinsic]
unsafe fn raw_eq<T>(a: &T, b: &T) -> bool;

fn usize_eq(a: usize, b: usize) -> bool {
    unsafe { raw_eq(&a, &b) }
}

#[repr(C)]
struct FatPtr {
    data: *const (),
    vtable: *const [usize; 4],
}
impl Copy for FatPtr {}

#[repr(C)]
struct FatPtrMut {
    data: *mut (),
    vtable: *const [usize; 4],
}
impl Copy for FatPtrMut {}

#[lang = "start"]
fn start<T>(_main: fn() -> T, _argc: isize, _argv: *const *const u8, _sigpipe: u8) -> isize {
    _main();
    0
}
"""

MIRI_LITMUS_CASES: list[tuple[str, bool, str]] = [
    (
        "tb_01_guarded_icp_shared_fast_and_fallback_sound",
        True,
        r"""
pub trait ReadOp { fn eval(&self) -> usize; }
#[repr(C)] pub struct Alpha { pub v: usize }
#[repr(C)] pub struct CellBeta { pub cell: UnsafeCell<usize> }

impl ReadOp for Alpha {
    fn eval(&self) -> usize { wrapping_add(self.v, 1) }
}
impl ReadOp for CellBeta {
    fn eval(&self) -> usize {
        unsafe {
            let p = self.cell.get();
            *p = wrapping_add(*p, 10);
            *p
        }
    }
}

fn guarded_icp(op: &dyn ReadOp, known_alpha_vt: *const [usize; 4]) -> usize {
    let fp: FatPtr = unsafe { transmute(op) };
    if usize_eq(fp.vtable as usize, known_alpha_vt as usize) {
        let a: &Alpha = unsafe { &*(fp.data as *const Alpha) };
        Alpha::eval(a)
    } else {
        op.eval()
    }
}

fn main() {
    let a1 = Alpha { v: 41 };
    let a_dyn: &dyn ReadOp = &a1;
    let fp_a: FatPtr = unsafe { transmute(a_dyn) };
    let other_dso_vt_sentinel: [usize; 4] = [0, 0, 0, 0];

    let b1 = CellBeta { cell: UnsafeCell { value: 5 } };
    let b_dyn: &dyn ReadOp = &b1;

    // 1. Fast path hit (`fp.vtable == known_alpha_vt`)
    let r1 = guarded_icp(a_dyn, fp_a.vtable);
    // 2. Open-world vtable address mismatch (`fp.vtable != &other_dso_vt_sentinel`) -> safe indirect fallback
    let r2 = guarded_icp(a_dyn, &other_dso_vt_sentinel as *const [usize; 4]);
    // 3. UnsafeCell (`!Freeze`, `.Cell`) receiver miss -> safe indirect fallback mutating interior cell
    let r3 = guarded_icp(b_dyn, fp_a.vtable);
    if usize_eq(wrapping_add(wrapping_add(r1, r2), r3), 99) {} else { loop {} }
}
""",
    ),
    (
        "tb_02_guarded_icp_mut_protector_sound",
        True,
        r"""
pub trait MutOp { fn bump(&mut self, delta: usize) -> usize; }
#[repr(C)] pub struct Counter { pub n: usize }
impl MutOp for Counter {
    fn bump(&mut self, delta: usize) -> usize {
        self.n = wrapping_add(self.n, delta);
        self.n
    }
}

fn guarded_icp_mut(op: &mut dyn MutOp, known_vt: *const [usize; 4], delta: usize) -> usize {
    let raw_op: FatPtrMut = unsafe { transmute(&mut *op) };
    if usize_eq(raw_op.vtable as usize, known_vt as usize) {
        let c: &mut Counter = unsafe { &mut *(raw_op.data as *mut Counter) };
        Counter::bump(c, delta)
    } else {
        op.bump(delta)
    }
}

fn main() {
    let mut c1 = Counter { n: 10 };
    let known_vt: *const [usize; 4] = {
        let d: &mut dyn MutOp = &mut c1;
        let fp: FatPtrMut = unsafe { transmute(d) };
        fp.vtable
    };
    let other_dso_vt_sentinel: [usize; 4] = [0, 0, 0, 0];

    let v1 = guarded_icp_mut(&mut c1, known_vt, 5);
    let v2 = guarded_icp_mut(&mut c1, &other_dso_vt_sentinel as *const [usize; 4], 17);
    if usize_eq(wrapping_add(v1, v2), 47) {} else { loop {} }
}
""",
    ),
    (
        "tb_03_unguarded_stale_pgo_frozen_write_ub",
        False,
        r"""
pub trait SharedOp { fn run(&self) -> usize; }
#[repr(C)] pub struct FreezeAlpha { pub v: usize }
#[repr(C)] pub struct CellBeta { pub cell: UnsafeCell<usize> }

impl SharedOp for FreezeAlpha {
    fn run(&self) -> usize { self.v }
}
impl SharedOp for CellBeta {
    fn run(&self) -> usize {
        unsafe {
            let p = self.cell.get();
            *p = wrapping_add(*p, 1);
            *p
        }
    }
}

fn unguarded_stale_pgo_devirt(op: &dyn SharedOp) -> usize {
    let fp: FatPtr = unsafe { transmute(op) };
    let wrong: &CellBeta = unsafe { &*(fp.data as *const CellBeta) };
    CellBeta::run(wrong)
}

fn main() {
    let alpha = FreezeAlpha { v: 99 };
    let d: &dyn SharedOp = &alpha;
    let _ = unguarded_stale_pgo_devirt(d);
}
""",
    ),
    (
        "tb_04_closed_world_peeled_else_dup_vtable_ub",
        False,
        r"""
pub trait SharedOp { fn run(&self) -> usize; }
#[repr(C)] pub struct FreezeAlpha { pub v: usize }
#[repr(C)] pub struct CellBeta { pub cell: UnsafeCell<usize> }

impl SharedOp for FreezeAlpha {
    fn run(&self) -> usize { self.v }
}
impl SharedOp for CellBeta {
    fn run(&self) -> usize {
        unsafe {
            let p = self.cell.get();
            *p = wrapping_add(*p, 1);
            *p
        }
    }
}

fn closed_world_peeled_devirt(op: &dyn SharedOp, known_alpha_vt: *const [usize; 4]) -> usize {
    let fp: FatPtr = unsafe { transmute(op) };
    if usize_eq(fp.vtable as usize, known_alpha_vt as usize) {
        let a: &FreezeAlpha = unsafe { &*(fp.data as *const FreezeAlpha) };
        FreezeAlpha::run(a)
    } else {
        let b: &CellBeta = unsafe { &*(fp.data as *const CellBeta) };
        CellBeta::run(b)
    }
}

fn main() {
    let alpha = FreezeAlpha { v: 123 };
    let d: &dyn SharedOp = &alpha;
    let other_dso_alpha_vt: [usize; 4] = [0, 0, 0, 0];
    let _ = closed_world_peeled_devirt(d, &other_dso_alpha_vt as *const [usize; 4]);
}
""",
    ),
    (
        "tb_05_raw_vtable_deref_abstract_machine_ub",
        False,
        r"""
pub trait ReadOp { fn eval(&self) -> usize; }
#[repr(C)] pub struct Alpha { pub v: usize }
impl ReadOp for Alpha { fn eval(&self) -> usize { self.v } }

fn main() {
    let a = Alpha { v: 7 };
    let d: &dyn ReadOp = &a;
    let fp: FatPtr = unsafe { transmute(d) };
    // Dereferencing GlobalAlloc::VTable directly in Rust Abstract Machine is UB (size 0 allocation):
    let _words: [usize; 4] = unsafe { *fp.vtable };
}
""",
    ),
]


def run_experiment_3_miri_tree_borrows(tc: dict[str, str]) -> list[dict[str, Any]]:
    miri = tc["miri"]
    if not miri:
        return [{"status": "miri_not_installed"}]

    out: list[dict[str, Any]] = []
    with tempfile.TemporaryDirectory(prefix="miri_tb_icp_") as tmp:
        ws = pathlib.Path(tmp)
        for case_name, expect_ok, body in MIRI_LITMUS_CASES:
            src = ws / f"{case_name}.rs"
            src.write_text(MIRI_NOCORE_PRELUDE + "\n" + body)
            proc = run_cmd(
                [miri, "-Zmiri-tree-borrows", str(src)],
                cwd=ws,
                search_path=tc["search_path"],
                check=False,
            )
            passed = (proc.returncode == 0)
            ub_line = ""
            for ln in proc.stderr.splitlines():
                if "Undefined Behavior:" in ln:
                    ub_line = ln.strip()
                    break
            if passed != expect_ok:
                raise RuntimeError(
                    f"Miri litmus {case_name} unexpected exit={proc.returncode} "
                    f"(expected ok={expect_ok}):\n{proc.stderr}"
                )
            out.append({
                "case": case_name,
                "expected_sound": expect_ok,
                "exit_code": proc.returncode,
                "elapsed_ms": round(proc.elapsed_ms, 2),  # type: ignore[attr-defined]
                "miri_ub_diagnostic": ub_line,
            })
    return out


# ---------------------------------------------------------------------------
# Experiment 4: Native Runtime Dispatch Latency (`L4` Guarded ICP vs Indirect)
# ---------------------------------------------------------------------------

DISPATCH_BENCH_RS = r"""
use std::hint::black_box;
use std::time::Instant;

pub trait BenchOp {
    fn compute(&self, x: u64) -> u64;
}

#[repr(C)]
pub struct FastAlpha {
    pub k: u64,
}

#[repr(C)]
pub struct SlowBeta {
    pub m: u64,
}

impl BenchOp for FastAlpha {
    #[inline(always)]
    fn compute(&self, x: u64) -> u64 {
        x.wrapping_mul(3).wrapping_add(self.k)
    }
}

impl BenchOp for SlowBeta {
    #[inline(never)]
    fn compute(&self, x: u64) -> u64 {
        x.rotate_left(13) ^ self.m
    }
}

#[repr(C)]
#[derive(Copy, Clone)]
struct FatPtr {
    data: usize,
    vtable: usize,
}

#[inline(never)]
fn run_unpromoted_indirect(slice: &[&dyn BenchOp], rounds: usize) -> u64 {
    let mut acc = 1u64;
    for _ in 0..rounds {
        for op in slice {
            acc = op.compute(acc);
        }
    }
    acc
}

#[inline(never)]
fn run_fn_ptr_guarded(slice: &[&dyn BenchOp], target_fn: usize, rounds: usize) -> u64 {
    let mut acc = 1u64;
    for _ in 0..rounds {
        for &op in slice {
            let fp: FatPtr = unsafe { core::mem::transmute(op) };
            let slot_fn: usize = unsafe { *((fp.vtable as *const usize).add(3)) };
            if slot_fn == target_fn {
                let a: &FastAlpha = unsafe { &*(fp.data as *const FastAlpha) };
                acc = FastAlpha::compute(a, acc);
            } else {
                acc = op.compute(acc);
            }
        }
    }
    acc
}

#[inline(never)]
fn run_vptr_1slot_guarded(slice: &[&dyn BenchOp], target_vt1: usize, rounds: usize) -> u64 {
    let mut acc = 1u64;
    for _ in 0..rounds {
        for &op in slice {
            let fp: FatPtr = unsafe { core::mem::transmute(op) };
            if fp.vtable == target_vt1 {
                let a: &FastAlpha = unsafe { &*(fp.data as *const FastAlpha) };
                acc = FastAlpha::compute(a, acc);
            } else {
                acc = op.compute(acc);
            }
        }
    }
    acc
}

#[inline(never)]
fn run_vptr_2slot_guarded(slice: &[&dyn BenchOp], target_vt1: usize, target_vt2: usize, rounds: usize) -> u64 {
    let mut acc = 1u64;
    for _ in 0..rounds {
        for &op in slice {
            let fp: FatPtr = unsafe { core::mem::transmute(op) };
            if fp.vtable == target_vt1 || fp.vtable == target_vt2 {
                let a: &FastAlpha = unsafe { &*(fp.data as *const FastAlpha) };
                acc = FastAlpha::compute(a, acc);
            } else {
                acc = op.compute(acc);
            }
        }
    }
    acc
}

fn time_ns_per_call<F: FnMut() -> u64>(mut f: F, total_calls: usize, trials: usize) -> (f64, u64) {
    let mut samples = Vec::with_capacity(trials);
    let mut checksum = 0u64;
    // Warmup
    checksum ^= black_box(f());
    for _ in 0..trials {
        let t0 = Instant::now();
        checksum ^= black_box(f());
        let ns = t0.elapsed().as_nanos() as f64;
        samples.push(ns / (total_calls as f64));
    }
    samples.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (samples[trials / 2], checksum)
}

fn main() {
    let a = FastAlpha { k: 7 };
    let b = SlowBeta { m: 0xdead_beef };
    let a_dyn: &dyn BenchOp = black_box(&a);
    let b_dyn: &dyn BenchOp = black_box(&b);
    let fp_a: FatPtr = unsafe { core::mem::transmute(a_dyn) };
    let target_vt1 = fp_a.vtable;
    let target_fn = unsafe { *((target_vt1 as *const usize).add(3)) };

    // Duplicate vtable copy (modeling a second CGU or DSO with distinct vtable address):
    let dup_vtable_words: [usize; 4] = unsafe { *(target_vt1 as *const [usize; 4]) };
    let target_vt2 = dup_vtable_words.as_ptr() as usize;
    let a_dup_fp = FatPtr { data: fp_a.data, vtable: target_vt2 };
    let a_dup_dyn: &dyn BenchOp = unsafe { core::mem::transmute(a_dup_fp) };

    // Workload 1: Single-DSO (95% FastAlpha via vt1, 5% SlowBeta)
    let single_dso: [&dyn BenchOp; 20] = [
        a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn,
        a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, a_dyn, b_dyn,
    ];
    // Workload 2: Split-DSO/CGU (50% FastAlpha via vt1, 45% FastAlpha via vt2, 5% SlowBeta)
    let split_dso: [&dyn BenchOp; 20] = [
        a_dyn, a_dup_dyn, a_dyn, a_dup_dyn, a_dyn, a_dup_dyn, a_dyn, a_dup_dyn, a_dyn, a_dup_dyn,
        a_dyn, a_dup_dyn, a_dyn, a_dup_dyn, a_dyn, a_dup_dyn, a_dyn, a_dup_dyn, a_dyn, b_dyn,
    ];

    let rounds = 200_000usize;
    let total_calls = rounds * 20; // 4,000,000 calls per trial
    let trials = 7usize;

    let (ind_single_ns, c1) = time_ns_per_call(|| run_unpromoted_indirect(black_box(&single_dso), rounds), total_calls, trials);
    let (fn_single_ns, c2) = time_ns_per_call(|| run_fn_ptr_guarded(black_box(&single_dso), black_box(target_fn), rounds), total_calls, trials);
    let (vt1_single_ns, c3) = time_ns_per_call(|| run_vptr_1slot_guarded(black_box(&single_dso), black_box(target_vt1), rounds), total_calls, trials);

    let (ind_split_ns, c4) = time_ns_per_call(|| run_unpromoted_indirect(black_box(&split_dso), rounds), total_calls, trials);
    let (fn_split_ns, c5) = time_ns_per_call(|| run_fn_ptr_guarded(black_box(&split_dso), black_box(target_fn), rounds), total_calls, trials);
    let (vt1_split_ns, c6) = time_ns_per_call(|| run_vptr_1slot_guarded(black_box(&split_dso), black_box(target_vt1), rounds), total_calls, trials);
    let (vt2_split_ns, c7) = time_ns_per_call(|| run_vptr_2slot_guarded(black_box(&split_dso), black_box(target_vt1), black_box(target_vt2), rounds), total_calls, trials);

    assert_eq!(c1, c2);
    assert_eq!(c1, c3);
    assert_eq!(c4, c5);
    assert_eq!(c4, c6);
    assert_eq!(c4, c7);

    println!(
        "{{\"calls_per_trial\":{},\"trials\":{},\"single_dso_ns_per_call\":{{\"indirect\":{:.4},\"fn_ptr_guard_inlined\":{:.4},\"vptr_1slot_guard_inlined\":{:.4}}},\"split_dso_dup_vtable_ns_per_call\":{{\"indirect\":{:.4},\"fn_ptr_guard_shared_fn\":{:.4},\"vptr_1slot_guard_50pct_miss\":{:.4},\"vptr_2slot_guard_inlined\":{:.4}}}}}",
        total_calls, trials,
        ind_single_ns, fn_single_ns, vt1_single_ns,
        ind_split_ns, fn_split_ns, vt1_split_ns, vt2_split_ns,
    );
}
"""


def run_experiment_4_dispatch_latency(tc: dict[str, str]) -> dict[str, Any]:
    rustc = tc["rustc"]
    sp = tc["search_path"]
    with tempfile.TemporaryDirectory(prefix="icp_bench_") as tmp:
        ws = pathlib.Path(tmp)
        src = ws / "bench.rs"
        bin_p = ws / "bench_bin"
        src.write_text(DISPATCH_BENCH_RS)
        run_cmd(
            [rustc, str(src), "-C", "opt-level=3", "-C", "codegen-units=1", "-o", str(bin_p)],
            cwd=ws,
            search_path=sp,
        )
        rproc = run_cmd([str(bin_p)], cwd=ws, search_path=sp)
        res = json.loads(rproc.stdout.strip())
        res["note"] = (
            "Synthetic Rust source-level dispatch microbenchmark comparing indirect dispatch vs "
            "explicitly written function-pointer and 1-/2-slot vtable-pointer guards compiled "
            "with identical flags (`rustc -C opt-level=3 -C codegen-units=1`)."
        )
        return res


def main() -> int:
    tc = find_toolchains()
    rustc_vv = subprocess.check_output([tc["rustc"], "-vV"], text=True).strip()
    profdata_vv = subprocess.check_output([tc["llvm_profdata"], "--version"], text=True).strip()

    exp1 = run_experiment_1_vtable_matrix(tc)
    exp2 = run_experiment_2_pgo_vs_mir(tc)
    exp3 = run_experiment_3_miri_tree_borrows(tc)
    exp4 = run_experiment_4_dispatch_latency(tc)

    payload = {
        "environment": {
            "os": f"{platform.system()} {platform.machine()}",
            "arch": platform.machine(),
            "rustc_version_verbose": rustc_vv,
            "llvm_profdata_version": profdata_vv,
        },
        "experiment_1_vtable_deduplication_matrix": exp1,
        "experiment_2_pgo_cgu_lto_vs_canonical_mir": exp2,
        "experiment_3_miri_tree_borrows_litmus": exp3,
        "experiment_4_guard_microbenchmark": exp4,
    }

    out_path = pathlib.Path(__file__).resolve().parent / "probe_results.json"
    out_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")
    print(f"Wrote {out_path} ({out_path.stat().st_size} bytes)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
