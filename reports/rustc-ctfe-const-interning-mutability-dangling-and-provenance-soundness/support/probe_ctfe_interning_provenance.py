#!/usr/bin/env python3
"""Live rustc CTFE interning, mutability/UnsafeCell, dangling-pointer, and provenance probe suite."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

PROBES: dict[str, list[dict[str, object]]] = {
    "a_stack_mut_unsafe_cell_and_dangling": [
        {
            "id": "stack_mut_owned_cell_and_static_atomic_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
use core::cell::Cell;
use core::sync::atomic::{AtomicU32, Ordering};

const fn sum_via_mut(n: u32) -> u32 {
    let mut acc = 0;
    let mut i = 1;
    while i <= n {
        let r = &mut acc;
        *r += i;
        i += 1;
    }
    acc
}

const X: u32 = sum_via_mut(8) + 6;
const OWNED_CELL: Cell<u32> = Cell::new(10);
static ATOMIC: AtomicU32 = AtomicU32::new(77);
const STATIC_ATOMIC: &AtomicU32 = &ATOMIC;

fn main() {
    let c = OWNED_CELL;
    c.set(c.get() + 2);
    let prev = STATIC_ATOMIC.fetch_add(3, Ordering::SeqCst);
    let now = STATIC_ATOMIC.load(Ordering::SeqCst);
    println!("X={} CELL={} ATOMIC_PREV={} ATOMIC_NOW={}", X, c.get(), prev, now);
}
""",
        },
        {
            "id": "dangling_alloc_raw_ptr_in_final_const_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const DANGLE_RAW: *const u32 = {
    let x = 42u32;
    &raw const x
};

fn main() {
    let _ = DANGLE_RAW;
}
""",
        },
        {
            "id": "int_raw_ptr_stored_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
const INT_PTR: *const u32 = 0x1000usize as *const u32;

fn main() {
    println!("INT_PTR_ADDR={:#x}", INT_PTR.addr());
}
""",
        },
        {
            "id": "dangling_raw_deref_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const DEREF_DANGLE: u32 = {
    let p: *const u32 = {
        let x = 42u32;
        &raw const x
    };
    unsafe { *p }
};

fn main() {
    println!("{}", DEREF_DANGLE);
}
""",
        },
        {
            "id": "dangling_ref_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const DANGLE_REF: &u32 = unsafe {
    let p: *const u32 = {
        let x = 42u32;
        &raw const x
    };
    &*p
};

fn main() {
    println!("{}", *DANGLE_REF);
}
""",
        },
        {
            "id": "unsafe_cell_ref_in_const_rejected",
            "expect_compile_rc": 1,
            "code": r"""
use core::cell::UnsafeCell;

const BAD_CELL_REF: &UnsafeCell<u32> = &UnsafeCell::new(5);

fn main() {
    let _ = BAD_CELL_REF;
}
""",
        },
        {
            "id": "unsafe_cell_transmute_in_const_rejected",
            "expect_compile_rc": 1,
            "code": r"""
use core::cell::UnsafeCell;

const BAD_CELL_TRANSMUTE: &UnsafeCell<u32> = unsafe {
    core::mem::transmute::<&u32, &UnsafeCell<u32>>(&5u32)
};

fn main() {
    let _ = BAD_CELL_TRANSMUTE;
}
""",
        },
        {
            "id": "unsafe_cell_union_transmute_in_const_rejected",
            "expect_compile_rc": 1,
            "code": r"""
use core::cell::UnsafeCell;
use core::mem::ManuallyDrop;

#[repr(C)]
union CellOrInt {
    int: u32,
    cell: ManuallyDrop<UnsafeCell<u32>>,
}

const BAD_UNION_CELL: &CellOrInt = unsafe {
    core::mem::transmute::<&u32, &CellOrInt>(&5u32)
};

fn main() {
    let _ = BAD_UNION_CELL;
}
""",
        },
        {
            "id": "mut_ref_escaping_const_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const BAD_MUT_REF: &mut u32 = &mut 1u32;

fn main() {
    let _ = BAD_MUT_REF;
}
""",
        },
        {
            "id": "mut_ref_transmute_to_readonly_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const BAD_TRANSMUTE_MUT: &mut u32 = unsafe {
    let p: *const u32 = &1u32;
    core::mem::transmute::<*const u32, &mut u32>(p)
};

fn main() {
    let _ = BAD_TRANSMUTE_MUT;
}
""",
        },
        {
            "id": "zst_promoted_mut_and_zst_cell_exceptions_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
use core::cell::UnsafeCell;

const ZST_MUT_PROMOTED_OK: &[u8] = {
    let x: &mut [u8] = &mut [];
    x
};

const ZST_CELL_TRANSMUTE_OK: &UnsafeCell<()> = unsafe {
    core::mem::transmute::<&(), &UnsafeCell<()>>(&())
};

const ZST_MUT_TRANSMUTE_OK: &mut [u8; 0] = unsafe {
    let p: *const [u8; 0] = &[];
    core::mem::transmute::<*const [u8; 0], &mut [u8; 0]>(p)
};

fn main() {
    println!(
        "ZST_MUT_LEN={} ZST_CELL_SIZE={} ZST_MUT_ARR_LEN={}",
        ZST_MUT_PROMOTED_OK.len(),
        core::mem::size_of_val(ZST_CELL_TRANSMUTE_OK),
        ZST_MUT_TRANSMUTE_OK.len(),
    );
}
""",
        },
        {
            "id": "zst_unsafecell_direct_borrow_still_e0492_rejected",
            "expect_compile_rc": 1,
            "code": r"""
use core::cell::UnsafeCell;

const ZST_CELL_BORROW: &UnsafeCell<()> = &UnsafeCell::new(());

fn main() {
    let _ = ZST_CELL_BORROW;
}
""",
        },
        {
            "id": "static_mut_nested_mut_alloc_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
static mut S_MUT_SLICE: &mut [u32] = &mut [10, 20];

fn main() {
    unsafe {
        let p = &raw mut S_MUT_SLICE;
        let slice_ptr: *mut [u32] = *p;
        (*slice_ptr)[0] = 99;
        println!("S_MUT_0={} S_MUT_1={}", (*slice_ptr)[0], (*slice_ptr)[1]);
    }
}
""",
        },
    ],
    "b_ctfe_provenance_enforcement": [
        {
            "id": "provenance_valid_inbounds",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
const INBOUNDS_VAL: u32 = {
    let arr = [10u32, 20, 30, 40];
    unsafe { *arr.as_ptr().add(2) }
};

fn main() {
    println!("INBOUNDS_VAL={}", INBOUNDS_VAL);
}
""",
        },
        {
            "id": "int_to_ptr_deref_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const INT_PTR_DEREF: u8 = unsafe { *(0x1000usize as *const u8) };

fn main() {
    println!("{}", INT_PTR_DEREF);
}
""",
        },
        {
            "id": "int_to_ptr_zero_add_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
const INT_PTR_ZERO_ADD: *const u8 = unsafe { (0x1000usize as *const u8).add(0) };

fn main() {
    println!("INT_PTR_ZERO_ADD={:#x}", INT_PTR_ZERO_ADD.addr());
}
""",
        },
        {
            "id": "int_to_ptr_nonzero_add_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const INT_PTR_ADD_1: *const u8 = unsafe { (0x1000usize as *const u8).add(1) };

fn main() {
    let _ = INT_PTR_ADD_1;
}
""",
        },
        {
            "id": "oob_ptr_add_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const OOB_ADD: *const u8 = {
    let arr = [1u8, 2];
    unsafe { arr.as_ptr().add(10) }
};

fn main() {
    let _ = OOB_ADD;
}
""",
        },
        {
            "id": "oob_wrapping_add_static_stored_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
static ARR: [u8; 2] = [1u8, 2];
const OOB_WRAP_STATIC_PTR: *const u8 = ARR.as_ptr().wrapping_add(10);

fn main() {
    let diff = OOB_WRAP_STATIC_PTR.addr().wrapping_sub(ARR.as_ptr().addr());
    println!("OOB_WRAP_OFFSET={}", diff);
}
""",
        },
        {
            "id": "oob_wrapping_add_deref_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const WRAP_DEREF: u8 = {
    let arr = [1u8, 2];
    unsafe { *arr.as_ptr().wrapping_add(10) }
};

fn main() {
    let _ = WRAP_DEREF;
}
""",
        },
        {
            "id": "ptr_cmp_different_allocs_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const CMP_PTRS: bool = {
    let a = 1u8;
    let b = 2u8;
    (&raw const a) == (&raw const b)
};

fn main() {
    println!("{}", CMP_PTRS);
}
""",
        },
        {
            "id": "ptr_cmp_int_ptrs_rejected",
            "expect_compile_rc": 1,
            "code": r"""
const CMP_INT_PTRS: bool = (0x1000usize as *const u8) == (0x1000usize as *const u8);

fn main() {
    println!("{}", CMP_INT_PTRS);
}
""",
        },
        {
            "id": "ptr_to_int_cast_rejected",
            "expect_compile_rc": 1,
            "code": r"""
static S: u8 = 7;
const PTR_TO_INT: usize = (&raw const S) as usize;

fn main() {
    println!("{}", PTR_TO_INT);
}
""",
        },
        {
            "id": "offset_from_same_static_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
static A: [u32; 4] = [1, 2, 3, 4];
const SAME_DIFF: isize = unsafe { A.as_ptr().add(3).offset_from(A.as_ptr().add(1)) };

fn main() {
    println!("SAME_DIFF={}", SAME_DIFF);
}
""",
        },
        {
            "id": "offset_from_diff_alloc_rejected",
            "expect_compile_rc": 1,
            "code": r"""
static A: [u32; 4] = [1, 2, 3, 4];
static B: u32 = 9;
const CROSS_DIFF: isize = unsafe { (&raw const B).offset_from(A.as_ptr()) };

fn main() {
    println!("{}", CROSS_DIFF);
}
""",
        },
        {
            "id": "ptr_cmp_unleashed_runtime_binary_ptr_op_rejected",
            "expect_compile_rc": 1,
            "extra_args": ["-Z", "unleash-the-miri-inside-of-you"],
            "code": r"""
const CMP_UNLEASHED: bool = {
    let a = 1u8;
    let b = 2u8;
    (&raw const a) == (&raw const b)
};

fn main() {
    println!("{}", CMP_UNLEASHED);
}
""",
        },
    ],
    "c_const_referencing_static_and_static_mut": [
        {
            "id": "const_ref_to_static_atomic_and_ptr_to_static_mut_ok",
            "expect_compile_rc": 0,
            "expect_run_rc": 0,
            "code": r"""
use core::sync::atomic::{AtomicU32, Ordering};

static IMM_STATIC: u32 = 99;
static ATOMIC_STATIC: AtomicU32 = AtomicU32::new(5);
static mut MUT_STATIC: u32 = 123;

const REF_TO_IMM_STATIC: &u32 = &IMM_STATIC;
const READ_IMM_STATIC: u32 = IMM_STATIC;
const REF_TO_ATOMIC_STATIC: &AtomicU32 = &ATOMIC_STATIC;
const PTR_TO_MUT_STATIC: *mut u32 = &raw mut MUT_STATIC;

fn main() {
    let prev = REF_TO_ATOMIC_STATIC.fetch_add(2, Ordering::SeqCst);
    let now = REF_TO_ATOMIC_STATIC.load(Ordering::SeqCst);
    let after = unsafe {
        *PTR_TO_MUT_STATIC = 456;
        *PTR_TO_MUT_STATIC
    };
    println!(
        "REF_TO_STATIC={} READ_IMM_STATIC={} ATOMIC_PREV={} ATOMIC_NOW={} PTR_TO_MUT_STATIC_AFTER={}",
        *REF_TO_IMM_STATIC, READ_IMM_STATIC, prev, now, after
    );
}
""",
        },
        {
            "id": "const_read_atomic_static_rejected",
            "expect_compile_rc": 1,
            "code": r"""
use core::sync::atomic::AtomicU32;

static ATOMIC_STATIC: AtomicU32 = AtomicU32::new(5);
const READ_ATOMIC: u32 = unsafe { *(&raw const ATOMIC_STATIC as *const u32) };

fn main() {
    println!("{}", READ_ATOMIC);
}
""",
        },
        {
            "id": "const_reading_mut_static_rejected",
            "expect_compile_rc": 1,
            "code": r"""
static mut MUT_STATIC: u32 = 123;
const READ_MUT_STATIC: u32 = unsafe { MUT_STATIC };

fn main() {
    println!("{}", READ_MUT_STATIC);
}
""",
        },
        {
            "id": "const_transmute_imm_static_to_unsafecell_rejected",
            "expect_compile_rc": 1,
            "code": r"""
use core::cell::UnsafeCell;

static IMM_STATIC: u32 = 99;
const BAD_CELL_TO_IMM_STATIC: &UnsafeCell<u32> = unsafe {
    core::mem::transmute::<&u32, &UnsafeCell<u32>>(&IMM_STATIC)
};

fn main() {
    let _ = BAD_CELL_TO_IMM_STATIC;
}
""",
        },
    ],
}


def run_probe(rustc_bin: str, case: dict[str, object], tmp_dir: Path) -> dict[str, object]:
    probe_id = str(case["id"])
    src_path = tmp_dir / "probe.rs"
    bin_path = tmp_dir / "probe_bin"
    src_path.write_text(str(case["code"]).lstrip("\n"), encoding="utf-8")

    extra_args = [str(x) for x in case.get("extra_args", [])]
    home_dir = str(Path.home())
    cmd = [
        rustc_bin,
        "--edition=2024",
        f"--remap-path-prefix={home_dir}=<toolchain-home>",
        *extra_args,
        "probe.rs",
        "-o",
        "probe_bin",
    ]
    comp = subprocess.run(cmd, cwd=tmp_dir, capture_output=True, text=True, check=False)

    rec: dict[str, object] = {
        "edition": "2024",
        "extra_args": extra_args,
        "compile_returncode": comp.returncode,
        "compile_stdout": comp.stdout.strip(),
        "compile_stderr": comp.stderr.strip(),
    }
    if comp.returncode != case["expect_compile_rc"]:
        raise RuntimeError(
            f"Probe {probe_id} expected compile rc {case['expect_compile_rc']}, "
            f"got {comp.returncode}:\n{comp.stderr}"
        )
    if comp.returncode == 0:
        run = subprocess.run([str(bin_path)], capture_output=True, text=True, check=False)
        rec["run_returncode"] = run.returncode
        rec["run_stdout"] = run.stdout.strip()
        rec["run_stderr"] = run.stderr.strip()
        if run.returncode != case.get("expect_run_rc", 0):
            raise RuntimeError(
                f"Probe {probe_id} expected run rc {case.get('expect_run_rc', 0)}, "
                f"got {run.returncode}:\n{run.stderr}"
            )
    return rec


def main() -> int:
    rustc_bin = os.environ.get("RUSTC", "rustc")
    ver = subprocess.run(
        [rustc_bin, "--version", "--verbose"],
        capture_output=True,
        text=True,
        check=True,
    )
    commit_hash = ""
    for line in ver.stdout.splitlines():
        if line.startswith("commit-hash: "):
            commit_hash = line.split(": ", 1)[1].strip()
            break

    results: dict[str, dict[str, object]] = {}
    total = 0
    for cat, cases in PROBES.items():
        results[cat] = {}
        for case in cases:
            total += 1
            with tempfile.TemporaryDirectory() as td:
                results[cat][str(case["id"])] = run_probe(rustc_bin, case, Path(td))

    out = {
        "probe_suite": "ctfe_const_interning_mutability_dangling_and_provenance",
        "rust_commit_sha": commit_hash,
        "rustc_version": ver.stdout.strip(),
        "total_cases": total,
        "experiments": results,
    }
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
    else:
        print(json.dumps(out, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
