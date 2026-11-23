#!/usr/bin/env python3
"""Reproducible probe of LLVM GlobalOpt / InstCombine / SROA / DSE boundaries
for x86_64 SeqCst, non-SeqCst RMW, compare_exchange, and compiler_fence
under rustc -Copt-level=3 -Clto=fat across both cdylib and bin LTO units.
"""

import pathlib
import re
import subprocess
import sys
import tempfile


CDYLIB_SRC = r"""
#![crate_type = "cdylib"]
extern crate alloc;
use alloc::boxed::Box;
use core::sync::atomic::{compiler_fence, fence, AtomicUsize, Ordering};

pub static X: AtomicUsize = AtomicUsize::new(0);
pub static Y: AtomicUsize = AtomicUsize::new(0);
pub static Z: AtomicUsize = AtomicUsize::new(0);
pub static PUB_ADDR: AtomicUsize = AtomicUsize::new(0);
pub static BIT_OUT: AtomicUsize = AtomicUsize::new(0);

static PRIV_WRITE_ONLY: AtomicUsize = AtomicUsize::new(0);
static PRIV_SAME_INIT: AtomicUsize = AtomicUsize::new(1);
static PRIV_DIFF_INIT_LOAD: AtomicUsize = AtomicUsize::new(0);
static PRIV_SWAP_SAME_INIT: AtomicUsize = AtomicUsize::new(1);
static PRIV_CAS_SAME_INIT: AtomicUsize = AtomicUsize::new(0);
static PRIV_DSE_TWO_STORES: AtomicUsize = AtomicUsize::new(0);

#[no_mangle]
pub extern "C" fn keep_io_live(vx: usize, vy: usize) -> usize {
    X.store(vx, Ordering::Relaxed);
    Y.store(vy, Ordering::Relaxed);
    Z.store(vx, Ordering::Relaxed);
    X.load(Ordering::Relaxed)
        .wrapping_add(Y.load(Ordering::Relaxed))
        .wrapping_add(Z.load(Ordering::Relaxed))
        .wrapping_add(PUB_ADDR.load(Ordering::Relaxed))
        .wrapping_add(BIT_OUT.load(Ordering::Relaxed))
        .wrapping_add(PRIV_SAME_INIT.load(Ordering::SeqCst))
        .wrapping_add(PRIV_DIFF_INIT_LOAD.load(Ordering::Relaxed))
        .wrapping_add(PRIV_DSE_TWO_STORES.load(Ordering::Relaxed))
}

#[no_mangle]
pub extern "C" fn elim_priv_write_only() -> usize {
    X.store(1, Ordering::Release);
    PRIV_WRITE_ONLY.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_priv_same_init() -> usize {
    X.store(1, Ordering::Release);
    PRIV_SAME_INIT.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_box_leaked_unescaped() -> usize {
    X.store(1, Ordering::Release);
    let b = Box::leak(Box::new(AtomicUsize::new(0)));
    b.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_local_expose_roundtrip() -> usize {
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    let ptr = core::ptr::with_exposed_provenance::<AtomicUsize>(addr);
    X.store(1, Ordering::Release);
    unsafe { (*ptr).store(1, Ordering::SeqCst); }
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn elim_local_branch_ne0() -> usize {
    X.store(1, Ordering::Relaxed);
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    if addr != 0 {
        local.store(1, Ordering::SeqCst);
    }
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_rlx() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::Relaxed);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_acq() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::Acquire);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_rel() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::Release);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn elim_idempotent_add0_acqrel() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::AcqRel);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn keep_hw_fence_sc() -> usize {
    X.store(1, Ordering::Release);
    fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_idempotent_add0_sc() -> usize {
    X.store(1, Ordering::Relaxed);
    let _ = Z.fetch_add(0, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn keep_published_exposed_addr() -> usize {
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    PUB_ADDR.store(addr, Ordering::Relaxed);
    X.store(1, Ordering::Release);
    local.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_branched_exposed_addr() -> usize {
    let local = AtomicUsize::new(0);
    let addr = (&local as *const AtomicUsize).expose_provenance();
    if (addr & 16) != 0 {
        BIT_OUT.store(1, Ordering::Relaxed);
    }
    X.store(1, Ordering::Release);
    local.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_priv_diff_init_with_load() -> usize {
    X.store(1, Ordering::Release);
    PRIV_DIFF_INIT_LOAD.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_priv_swap_same_init() -> usize {
    X.store(1, Ordering::Release);
    let _ = PRIV_SWAP_SAME_INIT.swap(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_priv_cas_same_init() -> usize {
    X.store(1, Ordering::Release);
    let _ = PRIV_CAS_SAME_INIT.compare_exchange(0, 0, Ordering::SeqCst, Ordering::Relaxed);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}

#[no_mangle]
pub extern "C" fn keep_dse_two_seqcst_stores() -> usize {
    PRIV_DSE_TWO_STORES.store(1, Ordering::SeqCst);
    X.store(1, Ordering::Release);
    PRIV_DSE_TWO_STORES.store(2, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Acquire)
}
"""

BIN_SRC = r"""
#![crate_type = "bin"]
use std::hint::black_box;
use std::sync::atomic::{compiler_fence, AtomicUsize, Ordering};

static X: AtomicUsize = AtomicUsize::new(0);
static Y: AtomicUsize = AtomicUsize::new(0);
static SINK_UNREAD: AtomicUsize = AtomicUsize::new(0);
pub static PUB_UNREAD_IN_BIN: AtomicUsize = AtomicUsize::new(0);
static PRIV_0LOAD: AtomicUsize = AtomicUsize::new(0);
static PRIV_SAME_0: AtomicUsize = AtomicUsize::new(0);
static PRIV_SAME_1: AtomicUsize = AtomicUsize::new(1);
static MP_DATA: AtomicUsize = AtomicUsize::new(0);
static MP_FLAG: AtomicUsize = AtomicUsize::new(0);

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_elim_dead_sink_local_store() -> usize {
    X.store(1, Ordering::Relaxed);
    let local = AtomicUsize::new(0);
    SINK_UNREAD.store((&local as *const AtomicUsize).expose_provenance(), Ordering::Relaxed);
    local.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_elim_pub_unread_store() -> usize {
    X.store(2, Ordering::Relaxed);
    PUB_UNREAD_IN_BIN.store(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_local_swap_same0() -> usize {
    X.store(3, Ordering::Relaxed);
    let local = AtomicUsize::new(0);
    let _ = local.swap(0, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_local_fetch_add0_sc() -> usize {
    X.store(4, Ordering::Relaxed);
    let local = AtomicUsize::new(0);
    let _ = local.fetch_add(0, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_local_fetch_or0_sc() -> usize {
    X.store(5, Ordering::Relaxed);
    let local = AtomicUsize::new(0);
    let _ = local.fetch_or(0, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_local_cas_weak_same0() -> usize {
    X.store(6, Ordering::Relaxed);
    let local = AtomicUsize::new(0);
    let _ = local.compare_exchange_weak(0, 0, Ordering::SeqCst, Ordering::Relaxed);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_priv_cas_weak_fail_rlx() -> usize {
    X.store(7, Ordering::Relaxed);
    let _ = PRIV_SAME_0.compare_exchange_weak(99, 1, Ordering::SeqCst, Ordering::Relaxed);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_priv_0load_swap_sc() -> usize {
    X.store(8, Ordering::Relaxed);
    let _ = PRIV_0LOAD.swap(1, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_box_fetch_add0_sc() -> usize {
    X.store(9, Ordering::Relaxed);
    let b = Box::new(AtomicUsize::new(0));
    let _ = b.fetch_add(0, Ordering::SeqCst);
    compiler_fence(Ordering::SeqCst);
    Y.load(Ordering::Relaxed)
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_mp_cfence_rel() {
    MP_DATA.store(42, Ordering::Relaxed);
    compiler_fence(Ordering::Release);
    MP_FLAG.store(1, Ordering::Relaxed);
}

#[inline(never)]
#[no_mangle]
pub extern "C" fn bin_keep_mp_cfence_acq() -> usize {
    if MP_FLAG.load(Ordering::Relaxed) == 1 {
        compiler_fence(Ordering::Acquire);
        MP_DATA.load(Ordering::Relaxed)
    } else {
        0
    }
}

fn main() {
    black_box(bin_elim_dead_sink_local_store());
    black_box(bin_elim_pub_unread_store());
    black_box(bin_keep_local_swap_same0());
    black_box(bin_keep_local_fetch_add0_sc());
    black_box(bin_keep_local_fetch_or0_sc());
    black_box(bin_keep_local_cas_weak_same0());
    black_box(bin_keep_priv_cas_weak_fail_rlx());
    black_box(bin_keep_priv_0load_swap_sc());
    black_box(bin_keep_box_fetch_add0_sc());
    bin_keep_mp_cfence_rel();
    black_box(bin_keep_mp_cfence_acq());
    black_box(PRIV_SAME_0.load(Ordering::Relaxed));
    black_box(PRIV_SAME_1.load(Ordering::Relaxed));
    black_box(Y.swap(1, Ordering::Relaxed));
    black_box(X.load(Ordering::Relaxed));
}
"""


def extract_fn_asm(asm_text: str, fn_name: str) -> str:
    m = re.search(
        rf"(?ms)^\s*\.globl\s+{re.escape(fn_name)}\b.*?^{re.escape(fn_name)}:\n(.*?)^\.Lfunc_end",
        asm_text,
    )
    if m:
        return m.group(1)
    alias = re.search(rf"(?m)^{re.escape(fn_name)}\s*=\s*([A-Za-z0-9_.]+)\s*$", asm_text)
    if alias:
        return extract_fn_asm(asm_text, alias.group(1))
    raise AssertionError(f"missing function {fn_name} in assembly")


def has_serializing_atomic(body: str) -> bool:
    return bool(re.search(r"\b(xchgq|mfence|lock)\b", body))


def compile_asm(src_text: str, name: str, tmp: pathlib.Path) -> str:
    src = tmp / f"{name}.rs"
    asm = tmp / f"{name}.s"
    src.write_text(src_text, encoding="utf-8")
    subprocess.run(
        [
            "rustc",
            "--edition=2021",
            "--target=x86_64-unknown-linux-gnu",
            "-Copt-level=3",
            "-Clto=fat",
            "-Ccodegen-units=1",
            "--emit=asm",
            str(src),
            "-o",
            str(asm),
        ],
        check=True,
    )
    return asm.read_text(encoding="utf-8")


def main() -> int:
    rustc = subprocess.check_output(["rustc", "-vV"], text=True)
    with tempfile.TemporaryDirectory() as d:
        tmp = pathlib.Path(d)
        cdylib_asm = compile_asm(CDYLIB_SRC, "probe_cdylib", tmp)
        bin_asm = compile_asm(BIN_SRC, "probe_bin", tmp)

    cdylib_elim = [
        "elim_priv_write_only",
        "elim_priv_same_init",
        "elim_box_leaked_unescaped",
        "elim_local_expose_roundtrip",
        "elim_local_branch_ne0",
        "elim_idempotent_add0_rlx",
        "elim_idempotent_add0_acq",
        "elim_idempotent_add0_rel",
        "elim_idempotent_add0_acqrel",
    ]
    cdylib_keep = [
        "keep_hw_fence_sc",
        "keep_idempotent_add0_sc",
        "keep_published_exposed_addr",
        "keep_branched_exposed_addr",
        "keep_priv_diff_init_with_load",
        "keep_priv_swap_same_init",
        "keep_priv_cas_same_init",
        "keep_dse_two_seqcst_stores",
    ]
    bin_elim = [
        "bin_elim_dead_sink_local_store",
        "bin_elim_pub_unread_store",
    ]
    bin_keep = [
        "bin_keep_local_swap_same0",
        "bin_keep_local_fetch_add0_sc",
        "bin_keep_local_fetch_or0_sc",
        "bin_keep_local_cas_weak_same0",
        "bin_keep_priv_cas_weak_fail_rlx",
        "bin_keep_priv_0load_swap_sc",
        "bin_keep_box_fetch_add0_sc",
    ]

    for fn in cdylib_elim:
        body = extract_fn_asm(cdylib_asm, fn)
        assert not has_serializing_atomic(body), f"expected 0 xchg/lock in {fn}, got:\n{body}"
    for fn in cdylib_keep:
        body = extract_fn_asm(cdylib_asm, fn)
        assert has_serializing_atomic(body), f"expected xchg/lock in {fn}, got:\n{body}"
    dse_body = extract_fn_asm(cdylib_asm, "keep_dse_two_seqcst_stores")
    assert len(re.findall(r"\bxchgq\b", dse_body)) == 2, f"expected 2 xchgq in DSE check, got:\n{dse_body}"

    for fn in bin_elim:
        body = extract_fn_asm(bin_asm, fn)
        assert not has_serializing_atomic(body), f"expected 0 xchg/lock in {fn}, got:\n{body}"
    for fn in bin_keep:
        body = extract_fn_asm(bin_asm, fn)
        assert has_serializing_atomic(body), f"expected xchg/lock in {fn}, got:\n{body}"

    mp_rel = extract_fn_asm(bin_asm, "bin_keep_mp_cfence_rel")
    mp_acq = extract_fn_asm(bin_asm, "bin_keep_mp_cfence_acq")
    assert "#MEMBARRIER" in mp_rel and "#MEMBARRIER" in mp_acq, "expected #MEMBARRIER in MP compiler_fence cases"
    assert mp_rel.index("MP_DATA") < mp_rel.index("#MEMBARRIER") < mp_rel.index("MP_FLAG"), mp_rel
    assert mp_acq.index("MP_FLAG") < mp_acq.index("#MEMBARRIER") < mp_acq.index("MP_DATA"), mp_acq

    total_elim = len(cdylib_elim) + len(bin_elim)
    total_keep = len(cdylib_keep) + len(bin_keep) + 2
    print(f"PASS: x86_64 -Copt-level=3 -Clto=fat (cdylib + bin) boundary verified ({total_elim} eliminated, {total_keep} preserved).")
    for line in rustc.strip().splitlines()[:2]:
        print(" ", line)
    return 0


if __name__ == "__main__":
    sys.exit(main())
