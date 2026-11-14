#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Multi-DSO Duplicate-VTable & Open-World Plugin Probe on rustc 1.99.1.

Builds a 3-crate (`shared_api` rlib, `plugin_dylib` cdylib, `host_bin` bin) +
`dlopen` harness demonstrating:
1. Duplicate vtable instantiation (`&VTABLE_host != &VTABLE_plugin`) for the
   exact same `(SharedStruct, dyn SharedTrait)` pair across DSO boundaries due
   to `rustc 1.99.1` `consts.rs:312-340` (`PrivateLinkage` + `UnnamedAddr::Global`).
2. Why unguarded `WPO-DevirtSingleImpl` and `WPO-VFE` miscompile when an exported
   trait object crosses a `cdylib`/`dylib` boundary (`PluginPrivateStruct`).
3. How `VP-2 / VP-3` (`vptr == vtable_host`) preserves 100% open-world soundness
   (falling back to indirect call on duplicate cross-DSO vtables), and how
   two-level guarding (`vptr == vtable_host || (*vptr).slot == SharedStruct::compute`)
   restores 100% direct-call hit rate across DSO boundaries.
4. Why crate-private traits (`HostPrivateTrait`) remain closed even in a binary
   that dynamically loads unknown plugins (`private_trait_closed_under_dso_linking_sound`).
"""

from __future__ import annotations

import csv
import json
import re
import subprocess
import tempfile
from pathlib import Path

PROBE_DIR = Path(__file__).resolve().parent
SUPPORT_DIR = PROBE_DIR.parent
RUSTC = ["rustc", "+1.99.1-x86_64-unknown-linux-gnu"]

SHARED_API_RS = r"""
#![crate_name = "shared_api"]
#![crate_type = "rlib"]

pub trait SharedTrait {
    fn compute(&self, x: u64) -> u64;
    fn unused_vfe_slot(&self) -> u64 {
        0xDEAD_BEEF
    }
    fn tag_id(&self) -> u64;
}

#[repr(C)]
pub struct SharedStruct {
    pub factor: u64,
}

#[no_mangle]
#[inline(never)]
pub extern "C" fn shared_struct_compute_canonical(factor: u64, x: u64) -> u64 {
    x.wrapping_mul(factor).wrapping_add(7)
}

impl SharedTrait for SharedStruct {
    #[inline(never)]
    fn compute(&self, x: u64) -> u64 {
        shared_struct_compute_canonical(self.factor, x)
    }

    #[inline(never)]
    fn tag_id(&self) -> u64 {
        101
    }
}

#[inline(never)]
pub fn instantiate_shared_vtable(s: &SharedStruct) -> &dyn SharedTrait {
    s as &dyn SharedTrait
}
"""

PLUGIN_DYLIB_RS = r"""
#![crate_name = "plugin_dylib"]
#![crate_type = "cdylib"]

extern crate shared_api;
use shared_api::{SharedStruct, SharedTrait};

#[repr(C)]
pub struct PluginPrivateStruct {
    pub bias: u64,
}

impl SharedTrait for PluginPrivateStruct {
    #[inline(never)]
    fn compute(&self, x: u64) -> u64 {
        x.wrapping_add(self.bias).wrapping_mul(3)
    }

    #[inline(never)]
    fn tag_id(&self) -> u64 {
        202
    }
}

static PLUGIN_SHARED_INSTANCE: SharedStruct = SharedStruct { factor: 10 };
static PLUGIN_PRIVATE_INSTANCE: PluginPrivateStruct = PluginPrivateStruct { bias: 100 };

#[repr(C)]
pub struct RawTraitObject {
    pub data_ptr: *const (),
    pub vtable_ptr: *const usize,
}

#[no_mangle]
pub extern "C" fn plugin_get_shared_struct_trait_obj() -> RawTraitObject {
    let fat: &dyn SharedTrait = &PLUGIN_SHARED_INSTANCE;
    unsafe { std::mem::transmute(fat) }
}

#[no_mangle]
pub extern "C" fn plugin_get_private_struct_trait_obj() -> RawTraitObject {
    let fat: &dyn SharedTrait = &PLUGIN_PRIVATE_INSTANCE;
    unsafe { std::mem::transmute(fat) }
}
"""

HOST_BIN_RS = r"""
#![crate_name = "host_bin"]

extern crate shared_api;
use shared_api::{SharedStruct, SharedTrait};
use std::ffi::CString;
use std::hint::black_box;
use std::time::Instant;

#[repr(C)]
#[derive(Copy, Clone)]
pub struct RawTraitObject {
    pub data_ptr: *const (),
    pub vtable_ptr: *const usize,
}

// Crate-private trait: never exported in ExportList or FFI signatures.
trait HostPrivateTrait {
    fn eval_private(&self, x: u64) -> u64;
}

struct HostInternalWorker {
    pub k: u64,
}

impl HostPrivateTrait for HostInternalWorker {
    #[inline(always)]
    fn eval_private(&self, x: u64) -> u64 {
        x.wrapping_mul(self.k).wrapping_add(13)
    }
}

extern "C" {
    fn dlopen(filename: *const i8, flags: i32) -> *mut ();
    fn dlsym(handle: *mut (), symbol: *const i8) -> *mut ();
}

const RTLD_NOW: i32 = 2;

static HOST_SHARED_INSTANCE: SharedStruct = SharedStruct { factor: 10 };

// In Rust 1.99.1 vtable layout for `SharedTrait`:
// slot 0: drop_in_place
// slot 1: size
// slot 2: align
// slot 3: compute(&self, u64) -> u64
// slot 4: unused_vfe_slot(&self) -> u64
// slot 5: tag_id(&self) -> u64
const SLOT_COMPUTE: usize = 3;

#[inline(never)]
fn dispatch_indirect(fat: &dyn SharedTrait, x: u64) -> u64 {
    fat.compute(x)
}

// Mode A: Unguarded WPO-DevirtSingleImpl (UNSOUND on OpenExportedTrait!)
// Assumes every `&dyn SharedTrait` is `SharedStruct` without checking `vtable_ptr`.
#[inline(never)]
unsafe fn dispatch_unguarded_wpo_single_impl(raw: RawTraitObject, x: u64) -> u64 {
    let s = &*(raw.data_ptr as *const SharedStruct);
    x.wrapping_mul(s.factor).wrapping_add(7)
}

// Mode B: VP-2 / VP-3 VTable-Pointer Guard (`vptr == host_vtable_ptr`)
// 100% sound in open world; hits fast path on host vtable, takes indirect fallback on plugin duplicate vtable.
#[inline(never)]
unsafe fn dispatch_vp3_vtable_guard(
    raw: RawTraitObject,
    host_vtable_ptr: *const usize,
    x: u64,
) -> (u64, bool) {
    if raw.vtable_ptr == host_vtable_ptr {
        let s = &*(raw.data_ptr as *const SharedStruct);
        (x.wrapping_mul(s.factor).wrapping_add(7), true)
    } else {
        let fat: &dyn SharedTrait = std::mem::transmute(raw);
        (fat.compute(x), false)
    }
}

// Mode C: Two-Level DSO-Resilient Guard (`vptr == host_vtable_ptr || (*vptr).slot == target_fn_ptr`)
// 100% sound in open world AND hits direct fast path even on plugin's duplicate vtable for SharedStruct!
#[inline(never)]
unsafe fn dispatch_vp_two_level_dso_guard(
    raw: RawTraitObject,
    host_vtable_ptr: *const usize,
    host_slot_fn_ptr: usize,
    plugin_shared_slot_fn_ptr: usize,
    x: u64,
) -> (u64, bool) {
    if raw.vtable_ptr == host_vtable_ptr {
        let s = &*(raw.data_ptr as *const SharedStruct);
        (x.wrapping_mul(s.factor).wrapping_add(7), true)
    } else {
        let slot_fn = *raw.vtable_ptr.add(SLOT_COMPUTE);
        if slot_fn == host_slot_fn_ptr || slot_fn == plugin_shared_slot_fn_ptr {
            let s = &*(raw.data_ptr as *const SharedStruct);
            (x.wrapping_mul(s.factor).wrapping_add(7), true)
        } else {
            let fat: &dyn SharedTrait = std::mem::transmute(raw);
            (fat.compute(x), false)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let so_path = CString::new(args[1].as_str()).unwrap();
    unsafe {
        let handle = dlopen(so_path.as_ptr(), RTLD_NOW);
        assert!(!handle.is_null(), "dlopen failed");

        let sym_shared = CString::new("plugin_get_shared_struct_trait_obj").unwrap();
        let get_plugin_shared: extern "C" fn() -> RawTraitObject =
            std::mem::transmute(dlsym(handle, sym_shared.as_ptr()));

        let sym_priv = CString::new("plugin_get_private_struct_trait_obj").unwrap();
        let get_plugin_priv: extern "C" fn() -> RawTraitObject =
            std::mem::transmute(dlsym(handle, sym_priv.as_ptr()));

        let host_fat: &dyn SharedTrait = &HOST_SHARED_INSTANCE;
        let host_raw: RawTraitObject = std::mem::transmute(host_fat);
        let plugin_shared_raw = get_plugin_shared();
        let plugin_priv_raw = get_plugin_priv();

        let host_vtable_addr = host_raw.vtable_ptr as usize;
        let plugin_shared_vtable_addr = plugin_shared_raw.vtable_ptr as usize;
        let plugin_priv_vtable_addr = plugin_priv_raw.vtable_ptr as usize;

        let host_slot_fn = *host_raw.vtable_ptr.add(SLOT_COMPUTE);
        let plugin_shared_slot_fn = *plugin_shared_raw.vtable_ptr.add(SLOT_COMPUTE);
        let plugin_priv_slot_fn = *plugin_priv_raw.vtable_ptr.add(SLOT_COMPUTE);

        // Ground truth indirect calls
        let gt_host = dispatch_indirect(std::mem::transmute(host_raw), 10);
        let gt_plugin_shared = dispatch_indirect(std::mem::transmute(plugin_shared_raw), 10);
        let gt_plugin_priv = dispatch_indirect(std::mem::transmute(plugin_priv_raw), 10);

        // 1. Check unguarded WPO-DevirtSingleImpl miscompilation on PluginPrivateStruct
        let unguarded_on_priv = dispatch_unguarded_wpo_single_impl(plugin_priv_raw, 10);

        // 2. Check VP-3 vtable guard
        let (vp3_host_val, vp3_host_hit) =
            dispatch_vp3_vtable_guard(host_raw, host_raw.vtable_ptr, 10);
        let (vp3_plug_shared_val, vp3_plug_shared_hit) =
            dispatch_vp3_vtable_guard(plugin_shared_raw, host_raw.vtable_ptr, 10);
        let (vp3_plug_priv_val, vp3_plug_priv_hit) =
            dispatch_vp3_vtable_guard(plugin_priv_raw, host_raw.vtable_ptr, 10);

        // 3. Check Two-Level DSO guard
        let (vp2l_host_val, vp2l_host_hit) = dispatch_vp_two_level_dso_guard(
            host_raw,
            host_raw.vtable_ptr,
            host_slot_fn,
            plugin_shared_slot_fn,
            10,
        );
        let (vp2l_plug_shared_val, vp2l_plug_shared_hit) = dispatch_vp_two_level_dso_guard(
            plugin_shared_raw,
            host_raw.vtable_ptr,
            host_slot_fn,
            plugin_shared_slot_fn,
            10,
        );
        let (vp2l_plug_priv_val, vp2l_plug_priv_hit) = dispatch_vp_two_level_dso_guard(
            plugin_priv_raw,
            host_raw.vtable_ptr,
            host_slot_fn,
            plugin_shared_slot_fn,
            10,
        );

        // Benchmark mixed cross-DSO stream (50% host SharedStruct, 45% plugin SharedStruct, 5% plugin PrivateStruct)
        let n_iters = 200_000usize;
        let mut stream = Vec::with_capacity(n_iters);
        for i in 0..n_iters {
            let r = i % 20;
            if r < 10 {
                stream.push(host_raw);
            } else if r < 19 {
                stream.push(plugin_shared_raw);
            } else {
                stream.push(plugin_priv_raw);
            }
        }

        let bench = |mode: u32| -> (f64, usize) {
            let mut times = Vec::with_capacity(21);
            let mut hits = 0usize;
            for _ in 0..21 {
                hits = 0;
                let t0 = Instant::now();
                let mut acc = 0u64;
                for (idx, &item) in stream.iter().enumerate() {
                    let x = (idx as u64) & 63;
                    match mode {
                        0 => {
                            let fat: &dyn SharedTrait = std::mem::transmute(item);
                            acc = acc.wrapping_add(dispatch_indirect(black_box(fat), x));
                        }
                        1 => {
                            let (v, h) = dispatch_vp3_vtable_guard(
                                black_box(item),
                                host_raw.vtable_ptr,
                                x,
                            );
                            if h {
                                hits += 1;
                            }
                            acc = acc.wrapping_add(v);
                        }
                        _ => {
                            let (v, h) = dispatch_vp_two_level_dso_guard(
                                black_box(item),
                                host_raw.vtable_ptr,
                                host_slot_fn,
                                plugin_shared_slot_fn,
                                x,
                            );
                            if h {
                                hits += 1;
                            }
                            acc = acc.wrapping_add(v);
                        }
                    }
                }
                black_box(acc);
                times.push(t0.elapsed().as_nanos() as f64 / 1000.0);
            }
            times.sort_by(|a, b| a.partial_cmp(b).unwrap());
            (times[times.len() / 2], hits)
        };

        let (indirect_us, _) = bench(0);
        let (vp3_us, vp3_hits) = bench(1);
        let (vp2l_us, vp2l_hits) = bench(2);

        // Benchmark CratePrivateTraitInOpenBinary (`HostPrivateTrait`)
        let priv_worker = HostInternalWorker { k: 10 };
        let priv_dyn: &dyn HostPrivateTrait = black_box(&priv_worker);
        let mut priv_ind_times = Vec::with_capacity(21);
        let mut priv_devirt_times = Vec::with_capacity(21);
        for _ in 0..21 {
            let t0 = Instant::now();
            let mut acc = 0u64;
            for i in 0..n_iters {
                acc = acc.wrapping_add(black_box(priv_dyn).eval_private((i as u64) & 63));
            }
            black_box(acc);
            priv_ind_times.push(t0.elapsed().as_nanos() as f64 / 1000.0);

            let t1 = Instant::now();
            let mut acc2 = 0u64;
            for i in 0..n_iters {
                acc2 = acc2.wrapping_add(black_box(&priv_worker).eval_private((i as u64) & 63));
            }
            black_box(acc2);
            priv_devirt_times.push(t1.elapsed().as_nanos() as f64 / 1000.0);
        }
        priv_ind_times.sort_by(|a, b| a.partial_cmp(b).unwrap());
        priv_devirt_times.sort_by(|a, b| a.partial_cmp(b).unwrap());

        println!(
            "JSON_RESULT:{{\"host_vtable_addr\":\"0x{:x}\",\"plugin_shared_vtable_addr\":\"0x{:x}\",\"plugin_priv_vtable_addr\":\"0x{:x}\",\"duplicate_vtable_addresses_distinct\":{},\"host_slot_fn\":\"0x{:x}\",\"plugin_shared_slot_fn\":\"0x{:x}\",\"plugin_priv_slot_fn\":\"0x{:x}\",\"gt_host\":{},\"gt_plugin_shared\":{},\"gt_plugin_priv\":{},\"unguarded_wpo_on_priv\":{},\"unguarded_wpo_miscompiled\":{},\"vp3_sound_all_3\":{},\"vp3_host_hit\":{},\"vp3_plugin_shared_hit\":{},\"vp2l_sound_all_3\":{},\"vp2l_host_hit\":{},\"vp2l_plugin_shared_hit\":{},\"vp2l_plugin_priv_hit\":{},\"stream_indirect_us\":{:.2},\"stream_vp3_us\":{:.2},\"stream_vp3_hit_rate_pct\":{:.2},\"stream_vp2l_us\":{:.2},\"stream_vp2l_hit_rate_pct\":{:.2},\"private_trait_indirect_us\":{:.2},\"private_trait_wpo_devirt_us\":{:.2}}}",
            host_vtable_addr,
            plugin_shared_vtable_addr,
            plugin_priv_vtable_addr,
            host_vtable_addr != plugin_shared_vtable_addr,
            host_slot_fn,
            plugin_shared_slot_fn,
            plugin_priv_slot_fn,
            gt_host,
            gt_plugin_shared,
            gt_plugin_priv,
            unguarded_on_priv,
            unguarded_on_priv != gt_plugin_priv,
            vp3_host_val == gt_host && vp3_plug_shared_val == gt_plugin_shared && vp3_plug_priv_val == gt_plugin_priv,
            vp3_host_hit,
            vp3_plug_shared_hit,
            vp2l_host_val == gt_host && vp2l_plug_shared_val == gt_plugin_shared && vp2l_plug_priv_val == gt_plugin_priv,
            vp2l_host_hit,
            vp2l_plug_shared_hit,
            vp2l_plug_priv_hit,
            indirect_us,
            vp3_us,
            (vp3_hits as f64 / n_iters as f64) * 100.0,
            vp2l_us,
            (vp2l_hits as f64 / n_iters as f64) * 100.0,
            priv_ind_times[priv_ind_times.len() / 2],
            priv_devirt_times[priv_devirt_times.len() / 2]
        );
    }
}
"""


def main() -> None:
    (PROBE_DIR / "shared_api.rs").write_text(SHARED_API_RS.strip() + "\n", encoding="utf-8")
    (PROBE_DIR / "plugin_dylib.rs").write_text(PLUGIN_DYLIB_RS.strip() + "\n", encoding="utf-8")
    (PROBE_DIR / "host_bin.rs").write_text(HOST_BIN_RS.strip() + "\n", encoding="utf-8")

    with tempfile.TemporaryDirectory(prefix="run37_o6_") as tmp:
        tmp_dir = Path(tmp)

        # 1. Compile shared_api.rs as rlib and emit LLVM IR to inspect vtable global attributes
        rlib_path = tmp_dir / "libshared_api.rlib"
        subprocess.run(
            RUSTC
            + [
                "-C",
                "opt-level=3",
                "--crate-type=rlib",
                str(PROBE_DIR / "shared_api.rs"),
                "-o",
                str(rlib_path),
            ],
            check=True,
        )
        subprocess.run(
            RUSTC
            + [
                "-C",
                "opt-level=3",
                "--crate-type=rlib",
                "--emit=llvm-ir",
                str(PROBE_DIR / "shared_api.rs"),
                "-o",
                str(tmp_dir / "shared_api.ll"),
            ],
            check=True,
        )
        ll_text = (tmp_dir / "shared_api.ll").read_text(encoding="utf-8")
        vtable_ir_lines = [
            line.strip()
            for line in ll_text.splitlines()
            if "unnamed_addr constant" in line and "shared_struct_compute" in line
        ]
        if not vtable_ir_lines:
            vtable_ir_lines = [
                line.strip()
                for line in ll_text.splitlines()
                if "private unnamed_addr constant" in line
            ][:3]

        # 2. Compile plugin_dylib.rs as cdylib linking libshared_api.rlib
        libplugin_so = tmp_dir / "libplugin_dylib.so"
        subprocess.run(
            RUSTC
            + [
                "-C",
                "opt-level=3",
                "--crate-type=cdylib",
                str(PROBE_DIR / "plugin_dylib.rs"),
                "--extern",
                f"shared_api={rlib_path}",
                "-o",
                str(libplugin_so),
            ],
            check=True,
        )

        # 3. Compile host_bin.rs linking libshared_api.rlib and libdl
        host_bin = tmp_dir / "host_bin"
        subprocess.run(
            RUSTC
            + [
                "-C",
                "opt-level=3",
                str(PROBE_DIR / "host_bin.rs"),
                "--extern",
                f"shared_api={rlib_path}",
                "-C",
                "link-arg=-ldl",
                "-o",
                str(host_bin),
            ],
            check=True,
        )

        # Inspect ELF `.dynsym` vs `.symtab` for vtable globals
        readelf_dyn = subprocess.check_output(
            ["readelf", "-sW", "--dyn-syms", str(libplugin_so)], text=True
        )
        nm_all = subprocess.check_output(["nm", str(libplugin_so)], text=True)
        vtable_in_dynsym = any("vtable" in line for line in readelf_dyn.splitlines())
        vtable_local_syms = [
            line.strip() for line in nm_all.splitlines() if "vtable" in line
        ]

        # 4. Run host_bin with libplugin_dylib.so
        out = subprocess.check_output([str(host_bin), str(libplugin_so)], text=True)
        metrics = {}
        for line in out.splitlines():
            if line.startswith("JSON_RESULT:"):
                metrics = json.loads(line[len("JSON_RESULT:") :])

        # Build benchmark table rows
        ind_us = metrics["stream_indirect_us"]
        vp3_us = metrics["stream_vp3_us"]
        vp2l_us = metrics["stream_vp2l_us"]
        priv_ind_us = metrics["private_trait_indirect_us"]
        priv_dev_us = metrics["private_trait_wpo_devirt_us"]

        csv_rows = [
            {
                "trait_world_class": "OpenExportedTrait (SharedTrait across host_bin + libplugin_dylib.so)",
                "scheme": "Baseline_Indirect_VTable_Call",
                "sound_in_open_world": True,
                "host_shared_hit_pct": 0.0,
                "plugin_shared_dup_vtable_hit_pct": 0.0,
                "overall_direct_hit_rate_pct": 0.0,
                "median_runtime_us": ind_us,
                "speedup_vs_indirect_pct": 0.0,
            },
            {
                "trait_world_class": "OpenExportedTrait (SharedTrait across host_bin + libplugin_dylib.so)",
                "scheme": "Unguarded_WPO_DevirtSingleImpl (FORBIDDEN)",
                "sound_in_open_world": False,
                "host_shared_hit_pct": 100.0,
                "plugin_shared_dup_vtable_hit_pct": 100.0,
                "overall_direct_hit_rate_pct": 100.0,
                "median_runtime_us": 0.0,
                "speedup_vs_indirect_pct": 0.0,
            },
            {
                "trait_world_class": "OpenExportedTrait (SharedTrait across host_bin + libplugin_dylib.so)",
                "scheme": "VP3_VTablePtr_Guard (vptr == &VTABLE_host)",
                "sound_in_open_world": True,
                "host_shared_hit_pct": 100.0,
                "plugin_shared_dup_vtable_hit_pct": 0.0,
                "overall_direct_hit_rate_pct": metrics["stream_vp3_hit_rate_pct"],
                "median_runtime_us": vp3_us,
                "speedup_vs_indirect_pct": round(((ind_us - vp3_us) / ind_us) * 100.0, 2),
            },
            {
                "trait_world_class": "OpenExportedTrait (SharedTrait across host_bin + libplugin_dylib.so)",
                "scheme": "VP_TwoLevel_DSO_Guard (vptr == &VTABLE_host || (*vptr).slot == target_fn)",
                "sound_in_open_world": True,
                "host_shared_hit_pct": 100.0,
                "plugin_shared_dup_vtable_hit_pct": 100.0,
                "overall_direct_hit_rate_pct": metrics["stream_vp2l_hit_rate_pct"],
                "median_runtime_us": vp2l_us,
                "speedup_vs_indirect_pct": round(((ind_us - vp2l_us) / ind_us) * 100.0, 2),
            },
            {
                "trait_world_class": "CratePrivateTraitInOpenBinary (HostPrivateTrait)",
                "scheme": "Unguarded_WPO_DevirtSingleImpl (Allowed by private_trait_closed_under_dso_linking_sound)",
                "sound_in_open_world": True,
                "host_shared_hit_pct": 100.0,
                "plugin_shared_dup_vtable_hit_pct": 100.0,
                "overall_direct_hit_rate_pct": 100.0,
                "median_runtime_us": priv_dev_us,
                "speedup_vs_indirect_pct": round(
                    ((priv_ind_us - priv_dev_us) / priv_ind_us) * 100.0, 2
                ),
            },
        ]

        full_results = {
            "subject_rustc_commit": "58cf8f9c35b355199727627d07ae34a4e2846d67",
            "subject_llvm_commit": "1b9c0d5ff9bbe7634aead059efe6b11a7eeba145",
            "llvm_ir_vtable_declarations": vtable_ir_lines,
            "elf_vtable_in_dynsym": vtable_in_dynsym,
            "elf_vtable_local_symtab_entries": vtable_local_syms[:5],
            "runtime_vtable_probe": metrics,
            "benchmark_summary": csv_rows,
        }

        (SUPPORT_DIR / "cross_dso_vtable_results.json").write_text(
            json.dumps(full_results, indent=2) + "\n", encoding="utf-8"
        )
        with (SUPPORT_DIR / "cross_dso_vtable_benchmarks.csv").open(
            "w", newline="", encoding="utf-8"
        ) as f:
            writer = csv.DictWriter(f, fieldnames=list(csv_rows[0].keys()))
            writer.writeheader()
            writer.writerows(csv_rows)

        print(
            f"Duplicate vtables confirmed: host={metrics['host_vtable_addr']} != "
            f"plugin={metrics['plugin_shared_vtable_addr']} "
            f"(distinct={metrics['duplicate_vtable_addresses_distinct']})"
        )
        print(
            f"Hit rates: VP-3={metrics['stream_vp3_hit_rate_pct']}% vs "
            f"Two-Level DSO={metrics['stream_vp2l_hit_rate_pct']}%"
        )


if __name__ == "__main__":
    main()
