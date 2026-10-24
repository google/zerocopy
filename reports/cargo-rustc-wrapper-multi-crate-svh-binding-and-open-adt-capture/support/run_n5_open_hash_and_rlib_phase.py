#!/usr/bin/env python3
"""
N5 Open-Hash Acquisition & External .rlib optimized_mir vs Runtime(PostCleanup) Sidecar Probe
for joshlf/anneal#68 (§4.6 & §6 N5).
"""

import hashlib
import json
import os
import resource
import subprocess
import time

BASE_DIR = "/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/cargo-workspace-capture"
ART_DIR = os.path.join(BASE_DIR, "artifacts")
N5_SRC_DIR = os.path.join(BASE_DIR, "n5_probes_src")
DRIVER_BIN = "/tmp/direct_mir_driver_v4_bin"
TC_DIR = "/usr/local/google/home/joshlf/.anneal/toolchain/4791adccd9a0d457c1700a5eeec084d335a94a8ba17341cec727d22f6cc27f61"
RUSTC = os.path.join(TC_DIR, "rust/bin/rustc")
CHARON = os.path.join(TC_DIR, "aeneas/bin/charon")
LIB_DIR = os.path.join(TC_DIR, "rust/lib")
HOST_LIB_DIR = os.path.join(TC_DIR, "rust/lib/rustlib/x86_64-unknown-linux-gnu/lib")


def sha256_file(p: str) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(65536), b""):
            h.update(chunk)
    return h.hexdigest()


def run_cmd(run_id: str, cmd: list, out_paths: list):
    env = os.environ.copy()
    env["LD_LIBRARY_PATH"] = f"{LIB_DIR}:{HOST_LIB_DIR}:" + env.get("LD_LIBRARY_PATH", "")
    env["PATH"] = f"{TC_DIR}/rust/bin:{TC_DIR}/aeneas/bin:" + env.get("PATH", "")
    env["RUSTC"] = RUSTC
    env["CHARON_TOOLCHAIN_IS_IN_PATH"] = "1"
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    t0 = time.monotonic()
    proc = subprocess.run(cmd, cwd=BASE_DIR, env=env, capture_output=True, text=True, timeout=60)
    t1 = time.monotonic()
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    outputs = []
    for p in out_paths:
        if os.path.exists(p):
            outputs.append({
                "path": os.path.relpath(p, BASE_DIR),
                "size_bytes": os.path.getsize(p),
                "sha256": sha256_file(p),
            })
    return {
        "run_id": run_id,
        "cmd": cmd,
        "exit_code": proc.returncode,
        "wall_ms": round((t1 - t0) * 1000.0, 2),
        "max_rss_kib": max(r0.ru_maxrss, r1.ru_maxrss),
        "stdout_tail": proc.stdout[-400:] if proc.stdout else "",
        "stderr_tail": proc.stderr[-400:] if proc.stderr else "",
        "outputs": outputs,
    }


RING_WINDOW_PROBE_RS = """#![no_std]
use core::marker::PhantomData;

#[repr(C)]
pub struct QuotaCell<T, const LIMIT: usize> {
    pub cursor: usize,
    pub _marker: PhantomData<T>,
}

#[inline(never)]
pub unsafe fn advance_quota<T, const LIMIT: usize>(
    cell_ptr: *const T,
    base: usize,
    step: usize,
) -> usize {
    let _ = *cell_ptr;
    let align = core::mem::align_of::<T>();
    let next = base.wrapping_add(align);
    let stepped = next.wrapping_add(step);
    stepped.wrapping_add(LIMIT)
}

pub unsafe fn verify_two_instances(
    p32: *const u32,
    p64: *const u64,
    base: usize,
) -> usize {
    let q1 = advance_quota::<u32, 4>(p32, base, 2);
    let q2 = advance_quota::<u64, 8>(p64, q1, 3);
    q2
}
"""

RING_WINDOW_PROBE_REFACTORED_RS = """#![no_std]
use core::marker::PhantomData;

#[repr(C)]
pub struct QuotaCell<T, const LIMIT: usize> {
    pub cursor: usize,
    pub _marker: PhantomData<T>,
}

#[inline(never)]
pub unsafe fn advance_quota<T, const LIMIT: usize>(
    raw_slot_ptr: *const T,
    initial_cursor: usize,
    delta_stride: usize,
) -> usize {
    let _ = *raw_slot_ptr;
    let ty_align = core::mem::align_of::<T>();
    let with_stride = initial_cursor.wrapping_add(delta_stride);
    let with_align = with_stride.wrapping_add(ty_align);
    with_align.wrapping_add(LIMIT)
}

pub unsafe fn verify_two_instances(
    slot32: *const u32,
    slot64: *const u64,
    seed_base: usize,
) -> usize {
    let first_window = advance_quota::<u32, 4>(slot32, seed_base, 2);
    let combined_window = advance_quota::<u64, 8>(slot64, first_window, 3);
    combined_window
}
"""

EXT_PHASE_LIB_RS = """#![no_std]

#[inline(never)]
pub unsafe fn ext_probe_mention_and_storage(ptr: *const u32, x: usize) -> usize {
    let _ = *ptr;
    let stepped = x.wrapping_add(4);
    stepped
}
"""

EXT_PHASE_CLIENT_RS = """#![no_std]
extern crate ext_phase_lib;

pub unsafe fn client_rlib_vs_sidecar_entry(ptr: *const u32, x: usize) -> usize {
    let v = ext_phase_lib::ext_probe_mention_and_storage(ptr, x);
    v.wrapping_add(10)
}
"""

R5_INNER_LIB_RS = """#![no_std]

#[repr(C)]
pub struct WindowSpec {
    pub base: usize,
    pub span: usize,
}

#[repr(C)]
pub struct AuditCounter {
    pub steps: u32,
    pub acc: u32,
}

impl AuditCounter {
    #[inline(never)]
    pub fn record_event(&mut self, tag: u32) {
        self.steps = self.steps.wrapping_add(1);
        self.acc = self.acc.wrapping_mul(16).wrapping_add(tag);
    }
}

pub struct ScopedTicket<'a> {
    pub tag: u32,
    pub counter: &'a mut AuditCounter,
}

impl<'a> Drop for ScopedTicket<'a> {
    #[inline(never)]
    fn drop(&mut self) {
        self.counter.record_event(self.tag);
    }
}

pub type OptionNonZeroU32 = core::option::Option<core::num::NonZeroU32>;

#[repr(C)]
pub struct ReprCPaddedHeader {
    pub tag: u8,
    pub count: u32,
    pub flags: u16,
}

#[repr(C, packed)]
pub struct PackedHeader {
    pub tag: u8,
    pub count: u32,
    pub tail: u8,
}

#[repr(C)]
pub struct PacketWithTail {
    pub magic: u32,
    pub flags: u16,
    pub payload: [u32],
}

#[inline(never)]
pub fn combine_window_total(spec: WindowSpec) -> usize {
    spec.base.wrapping_add(spec.span)
}
"""

R5_OUTER_LIB_RS = """#![no_std]
extern crate r5_inner_lib;
use r5_inner_lib::WindowSpec;

#[repr(C)]
pub struct QuotaPair {
    pub primary: usize,
    pub secondary: usize,
}

#[inline(never)]
pub fn build_quota_pair(spec: WindowSpec, weight: usize, bonus: usize) -> QuotaPair {
    let total = r5_inner_lib::combine_window_total(spec);
    QuotaPair {
        primary: total.wrapping_add(weight),
        secondary: bonus.wrapping_add(weight),
    }
}
"""

R5_CLIENT_APP_RS = """#![no_std]
extern crate r5_inner_lib;
extern crate r5_outer_lib;
use r5_inner_lib::{AuditCounter, ScopedTicket, WindowSpec};
use r5_outer_lib::QuotaPair;

#[inline(never)]
pub unsafe fn scale_window_aligned<T, const STRIDE: usize>(
    ptr: *const T,
    spec: WindowSpec,
) -> WindowSpec {
    let _ = *ptr;
    let align = core::mem::align_of::<T>();
    WindowSpec {
        base: spec.base.wrapping_add(align),
        span: spec.span.wrapping_add(STRIDE),
    }
}

pub unsafe fn execute_open_hash_pipeline(
    counter: &mut AuditCounter,
    p32: *const u32,
    p64: *const u64,
    seed_base: usize,
    early_commit: bool,
) -> usize {
    counter.record_event(5);
    let _ticket = ScopedTicket { tag: 9, counter };
    let w0 = WindowSpec {
        base: seed_base,
        span: 10,
    };
    let w1 = scale_window_aligned::<u32, 4>(p32, w0);
    let w2 = scale_window_aligned::<u64, 8>(p64, w1);
    let qp: QuotaPair = if early_commit {
        r5_outer_lib::build_quota_pair(w2, 2, 6)
    } else {
        r5_outer_lib::build_quota_pair(w2, 3, 12)
    };
    let out = qp.primary.wrapping_add(qp.secondary);
    out
}
"""

R5_CLIENT_APP_REFACTORED_RS = """#![no_std]
extern crate r5_inner_lib;
extern crate r5_outer_lib;
use r5_inner_lib::{AuditCounter, ScopedTicket, WindowSpec};
use r5_outer_lib::QuotaPair;

#[inline(never)]
pub unsafe fn scale_window_aligned<T, const STRIDE: usize>(
    raw_ptr: *const T,
    in_spec: WindowSpec,
) -> WindowSpec {
    let _ = *raw_ptr;
    let ty_align = core::mem::align_of::<T>();
    let next_span = in_spec.span.wrapping_add(STRIDE);
    let next_base = in_spec.base.wrapping_add(ty_align);
    WindowSpec {
        base: next_base,
        span: next_span,
    }
}

pub unsafe fn execute_open_hash_pipeline(
    audit_log: &mut AuditCounter,
    slot32: *const u32,
    slot64: *const u64,
    initial_base: usize,
    commit_fast: bool,
) -> usize {
    audit_log.record_event(5);
    let _guard_ticket = ScopedTicket {
        tag: 9,
        counter: audit_log,
    };
    let init_win = WindowSpec {
        base: initial_base,
        span: 10,
    };
    let win_after_u32 = scale_window_aligned::<u32, 4>(slot32, init_win);
    let win_after_u64 = scale_window_aligned::<u64, 8>(slot64, win_after_u32);
    let pair_res: QuotaPair = if commit_fast {
        r5_outer_lib::build_quota_pair(win_after_u64, 2, 6)
    } else {
        r5_outer_lib::build_quota_pair(win_after_u64, 3, 12)
    };
    let combined = pair_res.primary.wrapping_add(pair_res.secondary);
    combined
}
"""

R5_OVERWIDE_ADT_REJECT_RS = """#![no_std]

#[repr(C)]
pub struct OverwideRecord {
    pub a: usize,
    pub b: usize,
    pub c: usize,
    pub d: usize,
}

pub fn make_overwide(x: usize) -> OverwideRecord {
    OverwideRecord {
        a: x,
        b: x,
        c: x,
        d: x,
    }
}
"""

R6_EARLY_TYPE_ERROR_RS = """#![no_std]

pub fn broken_before_after_analysis(x: usize) -> usize {
    let y: bool = x;
    if y { 1 } else { 0 }
}
"""


def main():
    os.makedirs(ART_DIR, exist_ok=True)
    os.makedirs(N5_SRC_DIR, exist_ok=True)

    p_ring = os.path.join(N5_SRC_DIR, "ring_window_probe.rs")
    p_ring_ref = os.path.join(N5_SRC_DIR, "ring_window_probe_refactored.rs")
    p_ext_lib = os.path.join(N5_SRC_DIR, "ext_phase_lib.rs")
    p_ext_cli = os.path.join(N5_SRC_DIR, "ext_phase_client.rs")

    with open(p_ring, "w") as f:
        f.write(RING_WINDOW_PROBE_RS)
    with open(p_ring_ref, "w") as f:
        f.write(RING_WINDOW_PROBE_REFACTORED_RS)
    with open(p_ext_lib, "w") as f:
        f.write(EXT_PHASE_LIB_RS)
    with open(p_ext_cli, "w") as f:
        f.write(EXT_PHASE_CLIENT_RS)

    runs = []

    # 1. Capture ring_window_probe.rs via --driver-open-hash-mode
    ring_amir = os.path.join(ART_DIR, "n5_ring_window_probe.amir")
    ring_json = os.path.join(ART_DIR, "out_n5_ring_window_probe.json")
    ring_bodies = os.path.join(ART_DIR, "bodies_n5_ring_window_probe.json")
    ring_rlib = "/tmp/libn5_ring_window_probe.rlib"
    runs.append(run_cmd(
        "n5_open_hash_ring_window_probe",
        [
            DRIVER_BIN,
            p_ring,
            "--crate-name", "ring_window_probe",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", ring_json,
            "--driver-dump-bodies", ring_bodies,
            "--driver-emit-amir-v3", ring_amir,
            "-o", ring_rlib,
        ],
        [ring_amir, ring_json, ring_bodies],
    ))

    # 2. Capture ring_window_probe_refactored.rs via --driver-open-hash-mode
    ring_ref_amir = os.path.join(ART_DIR, "n5_ring_window_probe_refactored.amir")
    ring_ref_json = os.path.join(ART_DIR, "out_n5_ring_window_probe_refactored.json")
    ring_ref_bodies = os.path.join(ART_DIR, "bodies_n5_ring_window_probe_refactored.json")
    ring_ref_rlib = "/tmp/libn5_ring_window_probe_refactored.rlib"
    runs.append(run_cmd(
        "n5_open_hash_ring_window_probe_refactored",
        [
            DRIVER_BIN,
            p_ring_ref,
            "--crate-name", "ring_window_probe",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", ring_ref_json,
            "--driver-dump-bodies", ring_ref_bodies,
            "--driver-emit-amir-v3", ring_ref_amir,
            "-o", ring_ref_rlib,
        ],
        [ring_ref_amir, ring_ref_json, ring_ref_bodies],
    ))

    # 3. Capture ring_window_probe.rs via Charon 0.1.210 strongest flags
    ring_ullbc = os.path.join(ART_DIR, "n5_ring_window_probe_strongest.ullbc")
    runs.append(run_cmd(
        "n5_charon_ring_window_probe_strongest",
        [
            CHARON, "rustc",
            "--ullbc",
            "--precise-drops",
            "--mir", "elaborated",
            "--dest-file", ring_ullbc,
            "--",
            p_ring,
            "--crate-name", "ring_window_probe",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
        ],
        [ring_ullbc],
    ))

    # 4. External .rlib vs Runtime(PostCleanup) sidecar discriminator:
    # 4a. Capture ext_phase_lib as Runtime(PostCleanup) sidecar (-Z mir-preserve-ub) AND emit preserve-ub .rlib
    ext_sidecar_amir = os.path.join(ART_DIR, "n5_ext_phase_lib_sidecar.amir")
    ext_sidecar_json = os.path.join(ART_DIR, "out_n5_ext_phase_lib_sidecar.json")
    ext_sidecar_bodies = os.path.join(ART_DIR, "bodies_n5_ext_phase_lib_sidecar.json")
    ext_preserve_rlib = "/tmp/libext_phase_lib_preserve_ub.rlib"
    runs.append(run_cmd(
        "n5_ext_phase_lib_postcleanup_sidecar",
        [
            DRIVER_BIN,
            p_ext_lib,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", ext_sidecar_json,
            "--driver-dump-bodies", ext_sidecar_bodies,
            "--driver-emit-amir-v3", ext_sidecar_amir,
            "-o", ext_preserve_rlib,
        ],
        [ext_sidecar_amir, ext_sidecar_json, ext_sidecar_bodies],
    ))

    # 4b. Build default .rlib of ext_phase_lib (with -Z always-encode-mir=yes, default MIR optimization without -Z mir-preserve-ub)
    ext_default_rlib = "/tmp/libext_phase_lib_default.rlib"
    ext_default_json = os.path.join(ART_DIR, "out_n5_ext_phase_lib_default_rlib.json")
    runs.append(run_cmd(
        "n5_ext_phase_lib_default_rlib_build",
        [
            DRIVER_BIN,
            p_ext_lib,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", ext_default_json,
            "-o", ext_default_rlib,
        ],
        [ext_default_json],
    ))

    # 4c. Capture ext_phase_client importing default .rlib (reads tcx.optimized_mir from .rlib)
    cli_from_default_rlib_amir = os.path.join(ART_DIR, "n5_ext_phase_client_from_default_rlib.amir")
    cli_from_default_rlib_json = os.path.join(ART_DIR, "out_n5_ext_phase_client_from_default_rlib.json")
    cli_from_default_rlib_bodies = os.path.join(ART_DIR, "bodies_n5_ext_phase_client_from_default_rlib.json")
    runs.append(run_cmd(
        "n5_ext_phase_client_from_default_rlib",
        [
            DRIVER_BIN,
            p_ext_cli,
            "--crate-name", "ext_phase_client",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"ext_phase_lib={ext_default_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", cli_from_default_rlib_json,
            "--driver-dump-bodies", cli_from_default_rlib_bodies,
            "--driver-emit-amir-v3", cli_from_default_rlib_amir,
            "-o", "/tmp/libext_phase_client_default.rlib",
        ],
        [cli_from_default_rlib_amir, cli_from_default_rlib_json, cli_from_default_rlib_bodies],
    ))

    # 4d. Capture ext_phase_client importing preserve-ub .rlib (still reads tcx.optimized_mir phase 0x04 from .rlib!)
    cli_from_preserve_rlib_amir = os.path.join(ART_DIR, "n5_ext_phase_client_from_preserve_ub_rlib.amir")
    cli_from_preserve_rlib_json = os.path.join(ART_DIR, "out_n5_ext_phase_client_from_preserve_ub_rlib.json")
    cli_from_preserve_rlib_bodies = os.path.join(ART_DIR, "bodies_n5_ext_phase_client_from_preserve_ub_rlib.json")
    runs.append(run_cmd(
        "n5_ext_phase_client_from_preserve_ub_rlib",
        [
            DRIVER_BIN,
            p_ext_cli,
            "--crate-name", "ext_phase_client",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"ext_phase_lib={ext_preserve_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", cli_from_preserve_rlib_json,
            "--driver-dump-bodies", cli_from_preserve_rlib_bodies,
            "--driver-emit-amir-v3", cli_from_preserve_rlib_amir,
            "-o", "/tmp/libext_phase_client_preserve.rlib",
        ],
        [cli_from_preserve_rlib_amir, cli_from_preserve_rlib_json, cli_from_preserve_rlib_bodies],
    ))

    # =========================================================================
    # R5, R6, R7, R9, R10: 3-Crate Open-Hash Multi-Crate Workspace & Controls
    # =========================================================================
    p_r5_inner = os.path.join(N5_SRC_DIR, "r5_inner_lib.rs")
    p_r5_outer = os.path.join(N5_SRC_DIR, "r5_outer_lib.rs")
    p_r5_client = os.path.join(N5_SRC_DIR, "r5_client_app.rs")
    p_r5_client_ref = os.path.join(N5_SRC_DIR, "r5_client_app_refactored.rs")
    p_r5_overwide = os.path.join(N5_SRC_DIR, "r5_overwide_adt_reject.rs")
    p_r6_early_err = os.path.join(N5_SRC_DIR, "r6_early_type_error.rs")

    with open(p_r5_inner, "w") as f:
        f.write(R5_INNER_LIB_RS)
    with open(p_r5_outer, "w") as f:
        f.write(R5_OUTER_LIB_RS)
    with open(p_r5_client, "w") as f:
        f.write(R5_CLIENT_APP_RS)
    with open(p_r5_client_ref, "w") as f:
        f.write(R5_CLIENT_APP_REFACTORED_RS)
    with open(p_r5_overwide, "w") as f:
        f.write(R5_OVERWIDE_ADT_REJECT_RS)
    with open(p_r6_early_err, "w") as f:
        f.write(R6_EARLY_TYPE_ERROR_RS)

    # 5a. Build r5_inner_lib (with PacketWithTail unsized slice-tail #[repr(C)] layout query)
    r5_inner_amir = os.path.join(ART_DIR, "r5_inner_lib_open_hash.amir")
    r5_inner_json = os.path.join(ART_DIR, "out_r5_inner_lib_open_hash.json")
    r5_inner_bodies = os.path.join(ART_DIR, "bodies_r5_inner_lib_open_hash.json")
    r5_inner_rlib = "/tmp/libr5_inner_lib.rlib"
    runs.append(run_cmd(
        "r5_inner_lib_open_hash",
        [
            DRIVER_BIN,
            p_r5_inner,
            "--crate-name", "r5_inner_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r5_inner_json,
            "--driver-dump-bodies", r5_inner_bodies,
            "--driver-emit-amir-v3", r5_inner_amir,
            "-o", r5_inner_rlib,
        ],
        [r5_inner_amir, r5_inner_json, r5_inner_bodies],
    ))

    # 5b. Build r5_outer_lib importing r5_inner_lib
    r5_outer_amir = os.path.join(ART_DIR, "r5_outer_lib_open_hash.amir")
    r5_outer_json = os.path.join(ART_DIR, "out_r5_outer_lib_open_hash.json")
    r5_outer_bodies = os.path.join(ART_DIR, "bodies_r5_outer_lib_open_hash.json")
    r5_outer_rlib = "/tmp/libr5_outer_lib.rlib"
    runs.append(run_cmd(
        "r5_outer_lib_open_hash",
        [
            DRIVER_BIN,
            p_r5_outer,
            "--crate-name", "r5_outer_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r5_outer_json,
            "--driver-dump-bodies", r5_outer_bodies,
            "--driver-emit-amir-v3", r5_outer_amir,
            "-o", r5_outer_rlib,
        ],
        [r5_outer_amir, r5_outer_json, r5_outer_bodies],
    ))

    # 5c. Build r5_client_app importing r5_inner_lib and r5_outer_lib (full 3-crate closure)
    r5_client_amir = os.path.join(ART_DIR, "r5_client_app_open_hash.amir")
    r5_client_json = os.path.join(ART_DIR, "out_r5_client_app_open_hash.json")
    r5_client_bodies = os.path.join(ART_DIR, "bodies_r5_client_app_open_hash.json")
    runs.append(run_cmd(
        "r5_client_app_open_hash",
        [
            DRIVER_BIN,
            p_r5_client,
            "--crate-name", "r5_client_app",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "--extern", f"r5_outer_lib={r5_outer_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r5_client_json,
            "--driver-dump-bodies", r5_client_bodies,
            "--driver-emit-amir-v3", r5_client_amir,
            "-o", "/tmp/libr5_client_app.rlib",
        ],
        [r5_client_amir, r5_client_json, r5_client_bodies],
    ))

    # 5d. Refactoring invariance on r5_client_app_refactored.rs
    r5_client_ref_amir = os.path.join(ART_DIR, "r5_client_app_refactored_open_hash.amir")
    r5_client_ref_json = os.path.join(ART_DIR, "out_r5_client_app_refactored_open_hash.json")
    r5_client_ref_bodies = os.path.join(ART_DIR, "bodies_r5_client_app_refactored_open_hash.json")
    runs.append(run_cmd(
        "r5_client_app_refactored_open_hash",
        [
            DRIVER_BIN,
            p_r5_client_ref,
            "--crate-name", "r5_client_app",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "--extern", f"r5_outer_lib={r5_outer_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r5_client_ref_json,
            "--driver-dump-bodies", r5_client_ref_bodies,
            "--driver-emit-amir-v3", r5_client_ref_amir,
            "-o", "/tmp/libr5_client_app_ref.rlib",
        ],
        [r5_client_ref_amir, r5_client_ref_json, r5_client_ref_bodies],
    ))

    # 5e. Forced hash collision control (--driver-hash-bucket-modulus 10: 10 symbols in 10 buckets forces linear-probing collision resolution!)
    r5_coll_amir = os.path.join(ART_DIR, "r5_client_app_forced_collision_mod10.amir")
    r5_coll_json = os.path.join(ART_DIR, "out_r5_client_app_forced_collision_mod10.json")
    runs.append(run_cmd(
        "r5_control_forced_hash_collision_modulus_10",
        [
            DRIVER_BIN,
            p_r5_client,
            "--crate-name", "r5_client_app",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "--extern", f"r5_outer_lib={r5_outer_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-hash-bucket-modulus", "10",
            "--driver-out-json", r5_coll_json,
            "--driver-emit-amir-v3", r5_coll_amir,
            "-o", "/tmp/libr5_client_app_coll.rlib",
        ],
        [r5_coll_amir, r5_coll_json],
    ))

    # 5f. Hash table exhaustion fail-closed control (--driver-hash-bucket-modulus 4)
    r5_exhaust_amir = os.path.join(ART_DIR, "r5_control_exhausted_mod4_should_not_exist.amir")
    r5_exhaust_json = os.path.join(ART_DIR, "out_r5_control_exhausted_mod4.json")
    runs.append(run_cmd(
        "r5_control_hash_table_exhausted_modulus_4_reject",
        [
            DRIVER_BIN,
            p_r5_client,
            "--crate-name", "r5_client_app",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "--extern", f"r5_outer_lib={r5_outer_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-hash-bucket-modulus", "4",
            "--driver-out-json", r5_exhaust_json,
            "--driver-emit-amir-v3", r5_exhaust_amir,
            "-o", "/tmp/libr5_client_app_exhaust.rlib",
        ],
        [r5_exhaust_amir, r5_exhaust_json],
    ))

    # 5g. Unclosed external dependency cap fail-closed control (--driver-max-external-bodies 2)
    r5_extcap_amir = os.path.join(ART_DIR, "r5_control_extcap2_should_not_exist.amir")
    r5_extcap_json = os.path.join(ART_DIR, "out_r5_control_extcap2_reject.json")
    runs.append(run_cmd(
        "r5_control_unclosed_external_cap_2_reject",
        [
            DRIVER_BIN,
            p_r5_client,
            "--crate-name", "r5_client_app",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "--extern", f"r5_outer_lib={r5_outer_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-max-external-bodies", "2",
            "--driver-out-json", r5_extcap_json,
            "--driver-emit-amir-v3", r5_extcap_amir,
            "-o", "/tmp/libr5_client_app_extcap.rlib",
        ],
        [r5_extcap_amir, r5_extcap_json],
    ))

    # 5h. Unsupported ADT arity (>= 4 fields) fail-closed control
    r5_overwide_amir = os.path.join(ART_DIR, "r5_control_overwide_should_not_exist.amir")
    r5_overwide_json = os.path.join(ART_DIR, "out_r5_control_overwide_adt_reject.json")
    runs.append(run_cmd(
        "r5_control_unsupported_adt_arity_4_reject",
        [
            DRIVER_BIN,
            p_r5_overwide,
            "--crate-name", "r5_overwide_adt_reject",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r5_overwide_json,
            "--driver-emit-amir-v3", r5_overwide_amir,
            "-o", "/tmp/libr5_overwide.rlib",
        ],
        [r5_overwide_amir, r5_overwide_json],
    ))

    # 5i. Matched 3-crate Charon 0.1.210 strongest-flags capture on r5_client_app
    r5_client_ullbc = os.path.join(ART_DIR, "r5_client_app_strongest.ullbc")
    runs.append(run_cmd(
        "r5_charon_client_app_strongest",
        [
            CHARON, "rustc",
            "--ullbc",
            "--precise-drops",
            "--extract-opaque-bodies",
            "--mir", "elaborated",
            "--dest-file", r5_client_ullbc,
            "--",
            p_r5_client,
            "--crate-name", "r5_client_app",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "--extern", f"r5_outer_lib={r5_outer_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
        ],
        [r5_client_ullbc],
    ))

    # 5j. Real on-disk default capture of r5_client_app WITHOUT -Z mir-preserve-ub (R9 / B1)
    r5_client_default_amir = os.path.join(ART_DIR, "r5_client_app_default_no_preserve_ub.amir")
    r5_client_default_json = os.path.join(ART_DIR, "out_r5_client_app_default_no_preserve_ub.json")
    r5_client_default_bodies = os.path.join(ART_DIR, "bodies_r5_client_app_default_no_preserve_ub.json")
    runs.append(run_cmd(
        "r5_client_app_default_no_preserve_ub",
        [
            DRIVER_BIN,
            p_r5_client,
            "--crate-name", "r5_client_app",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"r5_inner_lib={r5_inner_rlib}",
            "--extern", f"r5_outer_lib={r5_outer_rlib}",
            "-Z", "always-encode-mir=yes",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r5_client_default_json,
            "--driver-dump-bodies", r5_client_default_bodies,
            "--driver-emit-amir-v3", r5_client_default_amir,
            "-o", "/tmp/libr5_client_app_default.rlib",
        ],
        [r5_client_default_amir, r5_client_default_json, r5_client_default_bodies],
    ))

    # =========================================================================
    # R6 & R9: Phase 0x05 Rejection & Post-run_compiler Atomic Endorsement Controls
    # =========================================================================
    # 6a. MirPhase::Runtime(RuntimePhase::Initial) (0x05) explicit fail-closed rejection
    r6_init_phase_amir = os.path.join(ART_DIR, "r6_control_initial_phase_should_not_exist.amir")
    r6_init_phase_json = os.path.join(ART_DIR, "out_r6_control_initial_phase_reject.json")
    runs.append(run_cmd(
        "r6_control_mir_phase_runtime_initial_0x05_reject",
        [
            DRIVER_BIN,
            p_ext_lib,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-test-initial-phase-reject",
            "--driver-out-json", r6_init_phase_json,
            "--driver-emit-amir-v3", r6_init_phase_amir,
            "-o", "/tmp/libext_phase_init_reject.rlib",
        ],
        [r6_init_phase_amir, r6_init_phase_json],
    ))

    # 6b. Stale output pre-removal on early compilation failure BEFORE after_analysis
    r6_early_err_amir = os.path.join(ART_DIR, "r6_control_early_err_stale.amir")
    r6_early_err_json = os.path.join(ART_DIR, "out_r6_control_early_err_stale.json")
    with open(r6_early_err_amir, "wb") as f:
        f.write(b"AMIR\x03STALE_BYTES")
    with open(r6_early_err_json, "w") as f:
        f.write('{"amir_v3_status":"accepted_complete","post_run_compiler_verified":true}\n')
    runs.append(run_cmd(
        "r6_control_early_compile_error_preremoves_stale_outputs",
        [
            DRIVER_BIN,
            p_r6_early_err,
            "--crate-name", "r6_early_type_error",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r6_early_err_json,
            "--driver-emit-amir-v3", r6_early_err_amir,
            "-o", "/tmp/libr6_early_err.rlib",
        ],
        [r6_early_err_amir, r6_early_err_json],
    ))

    # 6c. Interrupted before post-run_compiler endorsement
    r6_intr_amir = os.path.join(ART_DIR, "r6_control_interrupted_should_not_exist.amir")
    r6_intr_json = os.path.join(ART_DIR, "out_r6_control_interrupted_before_endorsement.json")
    runs.append(run_cmd(
        "r6_control_interrupted_before_endorsement_reject",
        [
            DRIVER_BIN,
            p_ext_lib,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-simulate-interrupted-before-endorsement",
            "--driver-out-json", r6_intr_json,
            "--driver-emit-amir-v3", r6_intr_amir,
            "-o", "/tmp/libext_phase_intr.rlib",
        ],
        [r6_intr_amir, r6_intr_json],
    ))

    # 6d. Post-after_analysis compiler error before endorsement
    r6_post_err_amir = os.path.join(ART_DIR, "r6_control_post_err_should_not_exist.amir")
    r6_post_err_json = os.path.join(ART_DIR, "out_r6_control_post_analysis_error.json")
    runs.append(run_cmd(
        "r6_control_post_analysis_compiler_error_reject",
        [
            DRIVER_BIN,
            p_ext_lib,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-inject-post-analysis-error",
            "--driver-out-json", r6_post_err_json,
            "--driver-emit-amir-v3", r6_post_err_amir,
            "-o", "/tmp/libext_phase_post_err.rlib",
        ],
        [r6_post_err_amir, r6_post_err_json],
    ))

    # 6e. out_json_path write failure (directory target) fails closed and removes .amir
    r6_json_dir = "/tmp/r6_out_json_is_dir"
    os.makedirs(r6_json_dir, exist_ok=True)
    r6_json_fail_amir = os.path.join(ART_DIR, "r6_control_json_write_fail_should_not_exist.amir")
    runs.append(run_cmd(
        "r6_control_out_json_write_failure_reject",
        [
            DRIVER_BIN,
            p_ext_lib,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", r6_json_dir,
            "--driver-emit-amir-v3", r6_json_fail_amir,
            "-o", "/tmp/libext_phase_json_fail.rlib",
        ],
        [r6_json_fail_amir],
    ))

    # =========================================================================
    # Q4 (#93 §9): Natural Post-after_analysis Linker Failure & Post-Staging Publication Failure
    # =========================================================================
    # 6f. Natural post-after_analysis linker failure (compiles rlib+cdylib so HIR crate hash is computed
    #     and after_analysis stages .amir.tmp.<pid> with zero errors, then fails naturally during cdylib linking
    #     via -C linker=/bin/false WITHOUT --driver-inject-post-analysis-error)
    p_q4_natural_link = os.path.join(N5_SRC_DIR, "q4_natural_linker_fail.rs")
    with open(p_q4_natural_link, "w") as f:
        f.write("""pub unsafe fn ext_probe_mention_and_storage(ptr: *const u32, x: usize) -> usize {
    let _ = *ptr;
    let stepped = x.wrapping_add(4);
    stepped
}
""")
    q4_natural_link_fail_amir = os.path.join(ART_DIR, "q4_natural_linker_fail_should_not_exist.amir")
    q4_natural_link_fail_json = os.path.join(ART_DIR, "out_q4_natural_post_analysis_linker_failure.json")
    runs.append(run_cmd(
        "q4_natural_post_analysis_linker_failure_reject",
        [
            DRIVER_BIN,
            p_q4_natural_link,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--crate-type=cdylib",
            "--edition=2021",
            "-C", "linker=/bin/false",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q4_natural_link_fail_json,
            "--driver-emit-amir-v3", q4_natural_link_fail_amir,
            "-o", "/tmp/libext_phase_natural_link_fail.so",
        ],
        [q4_natural_link_fail_amir, q4_natural_link_fail_json],
    ))

    # 6g. Post-staging rename failure AFTER after_analysis and run_compiler succeed
    q4_final_amir_dir = "/tmp/q4_final_amir_is_dir"
    os.makedirs(q4_final_amir_dir, exist_ok=True)
    q4_post_stage_fail_json = os.path.join(ART_DIR, "out_q4_post_staging_rename_failure.json")
    runs.append(run_cmd(
        "q4_post_staging_rename_failure_reject",
        [
            DRIVER_BIN,
            p_ext_lib,
            "--crate-name", "ext_phase_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q4_post_stage_fail_json,
            "--driver-emit-amir-v3", q4_final_amir_dir,
            "-o", "/tmp/libext_phase_post_stage_fail.rlib",
        ],
        [q4_post_stage_fail_json],
    ))

    # =========================================================================
    # Q3 (#93 §8): Producer-Level Challenge With Two Same-Shaped {u32, u32} Nominal Types
    # =========================================================================
    p_q3_lib = os.path.join(N5_SRC_DIR, "q3_nominal_pair_lib.rs")
    p_q3_cli = os.path.join(N5_SRC_DIR, "q3_nominal_pair_client.rs")
    p_q3_cli_ref = os.path.join(N5_SRC_DIR, "q3_nominal_pair_client_refactored.rs")
    p_q3_cli_swap_sig = os.path.join(N5_SRC_DIR, "q3_nominal_pair_client_swapped_sig.rs")
    p_q3_cli_type_err = os.path.join(N5_SRC_DIR, "q3_nominal_pair_client_type_error.rs")
    p_q3_drop_reject = os.path.join(N5_SRC_DIR, "q3_unsupported_drop_pair_reject.rs")

    with open(p_q3_lib, "w") as f:
        f.write("""#![no_std]

#[repr(C)]
pub struct MeterReading {
    pub ticks: u32,
    pub epoch: u32,
}

#[repr(C)]
pub struct LimitThreshold {
    pub min_ticks: u32,
    pub max_ticks: u32,
}

#[inline(never)]
pub fn make_meter_reading(base: u32, step: u32) -> MeterReading {
    MeterReading {
        ticks: base.wrapping_add(step),
        epoch: 1,
    }
}

#[inline(never)]
pub fn make_limit_threshold(floor: u32, span: u32) -> LimitThreshold {
    LimitThreshold {
        min_ticks: floor,
        max_ticks: floor.wrapping_add(span),
    }
}

#[inline(never)]
pub fn evaluate_reading_against_threshold(
    reading: MeterReading,
    threshold: LimitThreshold,
) -> u32 {
    let usable = reading.ticks.wrapping_add(threshold.min_ticks);
    usable.wrapping_add(threshold.max_ticks)
}
""")

    with open(p_q3_cli, "w") as f:
        f.write("""#![no_std]
extern crate q3_nominal_pair_lib;
use q3_nominal_pair_lib::{
    evaluate_reading_against_threshold, make_limit_threshold, make_meter_reading, LimitThreshold,
    MeterReading,
};

pub fn run_nominal_pair_pipeline(seed: u32, delta: u32) -> u32 {
    let reading: MeterReading = make_meter_reading(seed, delta);
    let epoch = reading.epoch;
    let threshold: LimitThreshold = make_limit_threshold(10, 20);
    let total = evaluate_reading_against_threshold(reading, threshold);
    total.wrapping_add(epoch)
}
""")

    with open(p_q3_cli_ref, "w") as f:
        f.write("""#![no_std]
extern crate q3_nominal_pair_lib;
use q3_nominal_pair_lib::{
    evaluate_reading_against_threshold, make_limit_threshold, make_meter_reading, LimitThreshold,
    MeterReading,
};

pub fn run_nominal_pair_pipeline(initial_seed: u32, step_delta: u32) -> u32 {
    let cur_reading: MeterReading = make_meter_reading(initial_seed, step_delta);
    let cur_epoch = cur_reading.epoch;
    let active_limit: LimitThreshold = make_limit_threshold(10, 20);
    let combined_score = evaluate_reading_against_threshold(cur_reading, active_limit);
    let final_score = combined_score.wrapping_add(cur_epoch);
    final_score
}
""")

    with open(p_q3_cli_swap_sig, "w") as f:
        f.write("""#![no_std]
extern crate q3_nominal_pair_lib;
use q3_nominal_pair_lib::{
    evaluate_reading_against_threshold, make_limit_threshold, make_meter_reading, LimitThreshold,
    MeterReading,
};

pub fn run_nominal_pair_pipeline(seed: u32, delta: u32) -> u32 {
    let first_slot: LimitThreshold = make_limit_threshold(10, 20);
    let floor_val = first_slot.min_ticks;
    let second_slot: MeterReading = make_meter_reading(seed, delta);
    let total = evaluate_reading_against_threshold(second_slot, first_slot);
    total.wrapping_add(floor_val)
}
""")

    with open(p_q3_cli_type_err, "w") as f:
        f.write("""#![no_std]
extern crate q3_nominal_pair_lib;
use q3_nominal_pair_lib::{
    evaluate_reading_against_threshold, make_limit_threshold, make_meter_reading, LimitThreshold,
    MeterReading,
};

pub fn run_nominal_pair_type_swap_error(seed: u32, delta: u32) -> u32 {
    let reading: MeterReading = make_meter_reading(seed, delta);
    let threshold: LimitThreshold = make_limit_threshold(10, 20);
    evaluate_reading_against_threshold(threshold, reading)
}
""")

    with open(p_q3_drop_reject, "w") as f:
        f.write("""#![no_std]

pub struct UnsupportedDropPair {
    pub a: usize,
    pub b: usize,
}

impl Drop for UnsupportedDropPair {
    fn drop(&mut self) {
        self.a = self.a.wrapping_add(self.b);
    }
}

pub fn use_unsupported_drop_pair(x: usize) -> usize {
    let p = UnsupportedDropPair { a: x, b: 1 };
    p.a
}
""")

    q3_lib_amir = os.path.join(ART_DIR, "q3_nominal_pair_lib.amir")
    q3_lib_json = os.path.join(ART_DIR, "out_q3_nominal_pair_lib.json")
    q3_lib_bodies = os.path.join(ART_DIR, "bodies_q3_nominal_pair_lib.json")
    q3_lib_rlib = "/tmp/libq3_nominal_pair_lib.rlib"
    runs.append(run_cmd(
        "q3_nominal_pair_lib_open_hash",
        [
            DRIVER_BIN,
            p_q3_lib,
            "--crate-name", "q3_nominal_pair_lib",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q3_lib_json,
            "--driver-dump-bodies", q3_lib_bodies,
            "--driver-emit-amir-v3", q3_lib_amir,
            "-o", q3_lib_rlib,
        ],
        [q3_lib_amir, q3_lib_json, q3_lib_bodies],
    ))

    q3_cli_amir = os.path.join(ART_DIR, "q3_nominal_pair_client.amir")
    q3_cli_json = os.path.join(ART_DIR, "out_q3_nominal_pair_client.json")
    q3_cli_bodies = os.path.join(ART_DIR, "bodies_q3_nominal_pair_client.json")
    runs.append(run_cmd(
        "q3_nominal_pair_client_open_hash",
        [
            DRIVER_BIN,
            p_q3_cli,
            "--crate-name", "q3_nominal_pair_client",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"q3_nominal_pair_lib={q3_lib_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q3_cli_json,
            "--driver-dump-bodies", q3_cli_bodies,
            "--driver-emit-amir-v3", q3_cli_amir,
            "-o", "/tmp/libq3_nominal_pair_client.rlib",
        ],
        [q3_cli_amir, q3_cli_json, q3_cli_bodies],
    ))

    q3_cli_ref_amir = os.path.join(ART_DIR, "q3_nominal_pair_client_refactored.amir")
    q3_cli_ref_json = os.path.join(ART_DIR, "out_q3_nominal_pair_client_refactored.json")
    runs.append(run_cmd(
        "q3_nominal_pair_client_refactored_open_hash",
        [
            DRIVER_BIN,
            p_q3_cli_ref,
            "--crate-name", "q3_nominal_pair_client",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"q3_nominal_pair_lib={q3_lib_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q3_cli_ref_json,
            "--driver-emit-amir-v3", q3_cli_ref_amir,
            "-o", "/tmp/libq3_nominal_pair_client_ref.rlib",
        ],
        [q3_cli_ref_amir, q3_cli_ref_json],
    ))

    q3_cli_swap_amir = os.path.join(ART_DIR, "q3_nominal_pair_client_swapped_sig.amir")
    q3_cli_swap_json = os.path.join(ART_DIR, "out_q3_nominal_pair_client_swapped_sig.json")
    runs.append(run_cmd(
        "q3_nominal_pair_client_swapped_sig_open_hash",
        [
            DRIVER_BIN,
            p_q3_cli_swap_sig,
            "--crate-name", "q3_nominal_pair_client",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"q3_nominal_pair_lib={q3_lib_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q3_cli_swap_json,
            "--driver-emit-amir-v3", q3_cli_swap_amir,
            "-o", "/tmp/libq3_nominal_pair_client_swap.rlib",
        ],
        [q3_cli_swap_amir, q3_cli_swap_json],
    ))

    q3_cli_type_err_amir = os.path.join(ART_DIR, "q3_nominal_pair_type_err_should_not_exist.amir")
    q3_cli_type_err_json = os.path.join(ART_DIR, "out_q3_nominal_pair_type_error.json")
    runs.append(run_cmd(
        "q3_nominal_pair_rust_type_swap_error_reject",
        [
            DRIVER_BIN,
            p_q3_cli_type_err,
            "--crate-name", "q3_nominal_pair_client",
            "--crate-type=rlib",
            "--edition=2021",
            "--extern", f"q3_nominal_pair_lib={q3_lib_rlib}",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q3_cli_type_err_json,
            "--driver-emit-amir-v3", q3_cli_type_err_amir,
            "-o", "/tmp/libq3_nominal_pair_type_err.rlib",
        ],
        [q3_cli_type_err_amir, q3_cli_type_err_json],
    ))

    q3_drop_reject_amir = os.path.join(ART_DIR, "q3_unsupported_drop_pair_should_not_exist.amir")
    q3_drop_reject_json = os.path.join(ART_DIR, "out_q3_unsupported_drop_pair_reject.json")
    runs.append(run_cmd(
        "q3_control_unsupported_two_field_drop_adt_reject",
        [
            DRIVER_BIN,
            p_q3_drop_reject,
            "--crate-name", "q3_unsupported_drop_pair_reject",
            "--crate-type=rlib",
            "--edition=2021",
            "-Z", "always-encode-mir=yes",
            "-Z", "mir-preserve-ub",
            "--driver-run-mono-collector",
            "--driver-open-hash-mode",
            "--driver-out-json", q3_drop_reject_json,
            "--driver-emit-amir-v3", q3_drop_reject_amir,
            "-o", "/tmp/libq3_drop_reject.rlib",
        ],
        [q3_drop_reject_amir, q3_drop_reject_json],
    ))

    # Verify zero hardcoded specimen-name strings exist in direct_mir_driver_v4.rs
    with open("/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/direct_mir_driver_v4.rs") as f:
        driver_src = f.read()
    unseen_identifiers = [
        "ring_window_probe",
        "QuotaCell",
        "advance_quota",
        "verify_two_instances",
        "ext_phase_lib",
        "ext_probe_mention_and_storage",
        "client_rlib_vs_sidecar_entry",
        "r5_inner_lib",
        "r5_outer_lib",
        "r5_client_app",
        "WindowSpec",
        "QuotaPair",
        "AuditCounter",
        "ScopedTicket",
        "OptionNonZeroU32",
        "ReprCPaddedHeader",
        "PackedHeader",
        "PacketWithTail",
        "combine_window_total",
        "build_quota_pair",
        "scale_window_aligned",
        "execute_open_hash_pipeline",
        "OverwideRecord",
        "q3_nominal_pair_lib",
        "q3_nominal_pair_client",
        "MeterReading",
        "LimitThreshold",
        "make_meter_reading",
        "make_limit_threshold",
        "evaluate_reading_against_threshold",
        "run_nominal_pair_pipeline",
        "UnsupportedDropPair",
    ]
    absent_in_driver = {ident: (ident not in driver_src) for ident in unseen_identifiers}

    ledger = {
        "experiment": "experiments/opsem/cargo-workspace-capture/n5-open-hash-and-rlib-phase",
        "issue_reference": "joshlf/anneal#68 (§4.6 & §6 N5), joshlf/anneal#89 (R5, R6, R7, R9, R10), and joshlf/anneal#93 (Q3, Q4)",
        "driver_sha256": sha256_file("/usr/local/google/home/joshlf/workspace/anneal/experiments/opsem/real-mir-ullbc-capture/direct_mir_driver_v4.rs"),
        "unseen_identifiers_absent_from_driver_source": absent_in_driver,
        "runs": runs,
    }
    ledger_path = os.path.join(BASE_DIR, "n5-open-hash-and-rlib-phase-ledger.json")
    with open(ledger_path, "w") as f:
        json.dump(ledger, f, indent=2)
    print(f"Wrote {ledger_path} with {len(runs)} runs.")
    for r in runs:
        print(f"  {r['run_id']}: exit={r['exit_code']}, wall={r['wall_ms']} ms, outputs={len(r['outputs'])}")


if __name__ == "__main__":
    main()
