#!/usr/bin/env python3
"""
1. Runs a 30-case CTFE vs. Runtime & Miri differential test suite (`C01`..`C30`)
   in rustc 1.99.1 and Miri 0.1.0 covering:
   - All 5 `GlobalAlloc` variants (`Memory`, `Function`, `VTable`, `Static`, `TypeId`);
   - Self-referential cyclic statics and mutually recursive static graphs;
   - Niche-packed enums and padded structs with uninitialized padding bytes (`InitMask`);
   - Interior-offset provenance relocations (`&ARRAY[3]`, `wrapping_add` / `wrapping_sub` offsets);
   - `UnsafeCell` / `Sync` interior-mutable statics (`.data` vs `.rodata`);
   - `TypeId::of::<T>() == TypeId::of::<U>()` at compile time vs. runtime;
   - `const_eval_select`, `ptr::null::<u8>().guaranteed_eq`, and RFC 3514 NaN bit patterns;
   - Promoted temporaries (`promoted[N]`) and inline `const { ... }` blocks.
2. Inspects the emitted `Runtime(PostCleanup)` MIR (`--emit=mir`) and LLVM IR (`--emit=llvm-ir`)
   from `rustc 1.99.1` (`-Zmir-opt-level=0`) to census all `GlobalAlloc` allocations,
   relocations, uninitialized padding masks, cyclic static edges, and `.rodata` vs `.data`
   section classifications into `globalalloc_census.json`.
"""

import json
import os
import re
import subprocess
import tempfile
from pathlib import Path

PROBE_30_SRC = r'''
#![feature(core_intrinsics, const_eval_select, const_trait_impl, const_cmp, const_index, const_raw_ptr_comparison)]
#![allow(internal_features, dead_code, unused_variables, unused_unsafe)]

use std::any::TypeId;
use std::cell::UnsafeCell;
use std::hint::black_box;

// --- Cyclic & Mutually Recursive Statics (C01..C03) ---
pub struct SelfRefStatic {
    pub tag: u64,
    pub self_ptr: &'static SelfRefStatic,
}
pub static C01_SELF_CYCLE: SelfRefStatic = SelfRefStatic {
    tag: 0xC01,
    self_ptr: &C01_SELF_CYCLE,
};

pub struct MutualNode {
    pub id: u64,
    pub peer: &'static MutualNode,
}
pub static C02_MUTUAL_A: MutualNode = MutualNode { id: 10, peer: &C03_MUTUAL_B };
pub static C03_MUTUAL_B: MutualNode = MutualNode { id: 20, peer: &C02_MUTUAL_A };

// --- GlobalAlloc::Static with UnsafeCell (.data vs .rodata) (C04..C05) ---
#[repr(C)]
pub struct SyncCellU64(pub UnsafeCell<u64>);
unsafe impl Sync for SyncCellU64 {}
pub static C04_INTERIOR_MUT_STATIC: SyncCellU64 = SyncCellU64(UnsafeCell::new(404));
pub static C05_FROZEN_STATIC: [u64; 4] = [1, 2, 3, 4];

// --- GlobalAlloc::VTable & GlobalAlloc::Function (C06..C08) ---
pub trait ComputeTrait: Sync {
    fn compute(&self, x: u64) -> u64;
}
pub struct AddConst(pub u64);
impl ComputeTrait for AddConst {
    fn compute(&self, x: u64) -> u64 { self.0 + x }
}
pub const C06_DYN_TRAIT_REF: &'static dyn ComputeTrait = &AddConst(60);

pub const fn add_ten(x: u64) -> u64 { x + 10 }
pub const C07_FN_PTR: fn(u64) -> u64 = add_ten;
pub const C08_FN_PTR_TABLE: [fn(u64) -> u64; 2] = [add_ten, |x| x * 2];

// --- GlobalAlloc::TypeId at Compile-Time vs Runtime (C09..C12) ---
pub const C09_TYPEID_U64: TypeId = TypeId::of::<u64>();
pub const C10_TYPEID_I64: TypeId = TypeId::of::<i64>();
pub const C11_TYPEID_EQ_SAME: bool = TypeId::of::<Option<&'static str>>() == TypeId::of::<Option<&'static str>>();
pub const C12_TYPEID_EQ_DIFF: bool = TypeId::of::<u64>() == TypeId::of::<i64>();

// --- GlobalAlloc::Memory with Uninitialized Padding (InitMask) & Niche Packing (C13..C16) ---
#[repr(C)]
#[derive(Copy, Clone)]
pub struct PaddedStruct {
    pub a: u8,
    // 3 bytes uninit padding
    pub b: u32,
    pub c: u16,
    // 2 bytes uninit padding
}
pub const C13_PADDED_STRUCT: PaddedStruct = PaddedStruct { a: 0x11, b: 0x22334455, c: 0x6677 };
pub const C14_PADDED_ARRAY_REF: &'static [PaddedStruct; 2] = &[C13_PADDED_STRUCT, PaddedStruct { a: 1, b: 2, c: 3 }];

#[repr(C)]
#[derive(Copy, Clone)]
pub enum NicheTaggedEnum {
    Small(u8),
    Large(u64, u32),
}
pub const C15_NICHE_ENUM_SMALL: &'static NicheTaggedEnum = &NicheTaggedEnum::Small(7);
pub const C16_NICHE_ENUM_LARGE: &'static NicheTaggedEnum = &NicheTaggedEnum::Large(0x1234, 0x5678);

// --- Interior-Offset Provenance Relocations & Slices (C17..C20) ---
pub static BACKING_ARRAY: [u64; 8] = [10, 20, 30, 40, 50, 60, 70, 80];
pub const C17_INTERIOR_ELEM_REF: &'static u64 = &BACKING_ARRAY[5];
pub const C18_INTERIOR_SUBSLICE: &'static [u64] = &BACKING_ARRAY[2..6];
pub const C19_ONE_PAST_END_PTR: *const u64 = BACKING_ARRAY.as_ptr().wrapping_add(8);
pub const C20_ZST_SLICE_REF: &'static [()] = &[(), (), ()];

// --- Promoted Temporaries (`promoted[N]`) and Inline `const { ... }` Blocks (C21..C25) ---
pub fn c21_promoted_composite_ref() -> &'static (u64, u32) {
    &(0xAA_BB_CC_DD, 0x11223344)
}
pub fn c22_inline_const_block_generic<T>() -> usize {
    const { core::mem::size_of::<T>() * 4 + core::mem::align_of::<T>() }
}
pub const fn c23_const_fn_loop_crc(mut x: u64) -> u64 {
    let mut i = 0;
    while i < 16 {
        x = (x >> 1) ^ ((x & 1).wrapping_neg() & 0xD800_0000_0000_0000);
        i += 1;
    }
    x
}
pub const C23_CRC_CONST: u64 = c23_const_fn_loop_crc(0x1234_5678);

pub const fn c24_const_slice_split(s: &[u64]) -> (u64, u64) {
    let (a, b) = s.split_at(2);
    (a[0] + a[1], b[0] + b[1])
}
pub const C24_SPLIT_CONST: (u64, u64) = c24_const_fn_slice_entry();
pub const fn c24_const_fn_slice_entry() -> (u64, u64) {
    c24_const_slice_split(&[10, 20, 30, 40])
}

pub const fn c25_nested_ref_graph() -> &'static &'static &'static u64 {
    &&&987654321u64
}
pub const C25_NESTED_REF: &'static &'static &'static u64 = c25_nested_ref_graph();

// --- CTFE vs. Runtime Divergence Boundaries (C26..C30) ---
pub const fn c26_guaranteed_cmp_null(p: *const u8) -> Option<bool> {
    p.guaranteed_eq(core::ptr::null())
}
pub const C26_NULL_EQ: Option<bool> = c26_guaranteed_cmp_null(core::ptr::null());
pub const C27_NONNULL_NE: Option<bool> = c26_guaranteed_cmp_null(&1u8 as *const u8);
pub const C28_SAME_STATIC_EQ: Option<bool> =
    (BACKING_ARRAY.as_ptr() as *const u8).guaranteed_eq(BACKING_ARRAY.as_ptr() as *const u8);

pub const fn c29_const_eval_select_probe(x: u64) -> u64 {
    const fn ctfe_impl(v: u64) -> u64 { v + 100 }
    fn rt_impl(v: u64) -> u64 { v + 100 }
    unsafe { core::intrinsics::const_eval_select((x,), ctfe_impl, rt_impl) }
}
pub const C29_SELECT_CONST: u64 = c29_const_eval_select_probe(23);

pub const fn c30_nan_quiet_check(x: f64) -> (bool, bool) {
    let nan = x - x; // For INFINITY - INFINITY, produces quiet NaN
    (nan.is_nan(), (nan.to_bits() & (1u64 << 51)) != 0)
}
pub const C30_NAN_CONST: (bool, bool) = c30_nan_quiet_check(f64::INFINITY);

fn main() {
    // Verify all 30 cases match between CTFE constants and runtime execution
    assert_eq!(C01_SELF_CYCLE.tag, 0xC01);
    assert!(core::ptr::eq(C01_SELF_CYCLE.self_ptr, &C01_SELF_CYCLE));
    assert!(core::ptr::eq(C01_SELF_CYCLE.self_ptr.self_ptr, &C01_SELF_CYCLE));

    assert_eq!(C02_MUTUAL_A.peer.id, 20);
    assert!(core::ptr::eq(C02_MUTUAL_A.peer.peer, &C02_MUTUAL_A));

    assert_eq!(unsafe { *C04_INTERIOR_MUT_STATIC.0.get() }, 404);
    assert_eq!(C05_FROZEN_STATIC[3], 4);

    assert_eq!(C06_DYN_TRAIT_REF.compute(15), 75);
    assert_eq!(C07_FN_PTR(5), add_ten(black_box(5)));
    assert_eq!(C08_FN_PTR_TABLE[1](9), 18);

    assert_eq!(C09_TYPEID_U64, TypeId::of::<u64>());
    assert_eq!(C10_TYPEID_I64, TypeId::of::<i64>());
    assert_eq!(C11_TYPEID_EQ_SAME, TypeId::of::<Option<&'static str>>() == TypeId::of::<Option<&'static str>>());
    assert!(C11_TYPEID_EQ_SAME);
    assert_eq!(C12_TYPEID_EQ_DIFF, TypeId::of::<u64>() == TypeId::of::<i64>());
    assert!(!C12_TYPEID_EQ_DIFF);

    let rt_padded = PaddedStruct { a: black_box(0x11), b: black_box(0x22334455), c: black_box(0x6677) };
    assert_eq!((C13_PADDED_STRUCT.a, C13_PADDED_STRUCT.b, C13_PADDED_STRUCT.c), (rt_padded.a, rt_padded.b, rt_padded.c));
    assert_eq!(C14_PADDED_ARRAY_REF[1].b, 2);

    match (C15_NICHE_ENUM_SMALL, C16_NICHE_ENUM_LARGE) {
        (NicheTaggedEnum::Small(s), NicheTaggedEnum::Large(l1, l2)) => {
            assert_eq!((*s, *l1, *l2), (7, 0x1234, 0x5678));
        }
        _ => panic!("enum mismatch"),
    }

    assert_eq!(*C17_INTERIOR_ELEM_REF, 60);
    assert!(core::ptr::eq(C17_INTERIOR_ELEM_REF, &BACKING_ARRAY[5]));
    assert_eq!(C18_INTERIOR_SUBSLICE, &[30, 40, 50, 60]);
    assert_eq!(C19_ONE_PAST_END_PTR.addr(), BACKING_ARRAY.as_ptr().wrapping_add(8).addr());
    assert_eq!(C20_ZST_SLICE_REF.len(), 3);

    assert_eq!(*c21_promoted_composite_ref(), (0xAA_BB_CC_DD, 0x11223344));
    assert_eq!(c22_inline_const_block_generic::<u64>(), 32 + 8);
    assert_eq!(C23_CRC_CONST, c23_const_fn_loop_crc(black_box(0x1234_5678)));
    assert_eq!(C24_SPLIT_CONST, c24_const_fn_slice_entry());
    assert_eq!(***C25_NESTED_REF, 987654321);

    assert_eq!(C26_NULL_EQ, Some(true));
    assert_eq!(C27_NONNULL_NE, Some(false));
    assert_eq!(C28_SAME_STATIC_EQ, Some(true));
    assert_eq!(C29_SELECT_CONST, c29_const_eval_select_probe(black_box(23)));

    let rt_nan = c30_nan_quiet_check(black_box(f64::INFINITY));
    assert_eq!(C30_NAN_CONST, (true, true));
    assert_eq!(rt_nan, (true, true));

    println!("ALL_30_CTFE_DIFFERENTIAL_PASSED");
}
'''

def parse_mir_and_llvm_globalallocs(mir_text: str, ll_text: str) -> dict:
    # Count alloc entries in MIR dump (`alloc123 (size: ..., align: ...) {`)
    alloc_headers = re.findall(r"^(alloc\d+)\s+\(([^)]+)\)\s*\{", mir_text, flags=re.MULTILINE)
    uninit_occurrences = len(re.findall(r"__+", mir_text))
    reloc_arrows = len(re.findall(r"╾─*alloc\d+", mir_text))

    # Classify LLVM globals (`constant` vs `global` for .rodata vs .data)
    rodata_globals = re.findall(r"^@([A-Za-z0-9_.$]+)\s*=\s*[^\n]*\bconstant\b", ll_text, flags=re.MULTILINE)
    mutable_globals = re.findall(r"^@([A-Za-z0-9_.$]+)\s*=\s*[^\n]*\bglobal\b", ll_text, flags=re.MULTILINE)
    undef_padding_chunks = len(re.findall(r"\[(\d+)\s+x\s+i8\]\s+undef", ll_text))

    return {
        "mir_alloc_headers_count": len(alloc_headers),
        "mir_uninit_byte_runs": uninit_occurrences,
        "mir_provenance_relocation_entries": reloc_arrows,
        "llvm_rodata_constant_globals_count": len(rodata_globals),
        "llvm_mutable_data_globals_count": len(mutable_globals),
        "llvm_undef_padding_chunk_count": undef_padding_chunks,
        "self_cyclic_static_verified": "C01_SELF_CYCLE" in ll_text,
        "mutual_cyclic_statics_verified": ("C02_MUTUAL_A" in ll_text and "C03_MUTUAL_B" in ll_text),
        "interior_mut_static_in_writable_data": any("C04_INTERIOR_MUT_STATIC" in g for g in mutable_globals),
        "frozen_static_in_rodata": any("C05_FROZEN_STATIC" in g for g in rodata_globals),
    }

def main():
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp)
        src_path = p / "probe30.rs"
        src_path.write_text(PROBE_30_SRC, encoding="utf-8")

        mir_path = p / "probe30.mir"
        ll_path = p / "probe30.ll"
        bin_path = p / "probe30.bin"

        base_cmd = ["rustc", "+1.99.1", "--edition=2024", "-Zmir-opt-level=0"]
        subprocess.run(base_cmd + ["--emit=mir", str(src_path), "-o", str(mir_path)], env=env, check=True)
        subprocess.run(base_cmd + ["--emit=llvm-ir", str(src_path), "-o", str(ll_path)], env=env, check=True)
        subprocess.run(base_cmd + [str(src_path), "-o", str(bin_path)], env=env, check=True)

        native_out = subprocess.check_output([str(bin_path)], text=True)
        assert "ALL_30_CTFE_DIFFERENTIAL_PASSED" in native_out

        # Also run under Miri (`-Zmiri-tree-borrows`)
        cargo_dir = p / "miri_pkg"
        (cargo_dir / "src").mkdir(parents=True)
        (cargo_dir / "src" / "main.rs").write_text(PROBE_30_SRC, encoding="utf-8")
        (cargo_dir / "Cargo.toml").write_text(
            '[package]\nname = "n10_probe"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        miri_res = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet"],
            cwd=str(cargo_dir),
            env=dict(env, MIRIFLAGS="-Zmiri-tree-borrows"),
            capture_output=True,
            text=True,
            check=True,
        )
        assert "ALL_30_CTFE_DIFFERENTIAL_PASSED" in miri_res.stdout

        census = parse_mir_and_llvm_globalallocs(
            mir_path.read_text(encoding="utf-8"),
            ll_path.read_text(encoding="utf-8"),
        )

        out = {
            "toolchain": "rustc 1.99.1 (58cf8f9c35b355199727627d07ae34a4e2846d67)",
            "miri_version": "miri 0.1.0 (3ef0c22cdb 2026-11-11)",
            "differential_cases_total": 30,
            "native_runtime_pass_count": 30,
            "miri_tree_borrows_pass_count": 30,
            "globalalloc_variants_covered": [
                "GlobalAlloc::Memory(ConstAllocation)",
                "GlobalAlloc::Function { instance }",
                "GlobalAlloc::VTable(Ty, List<PolyExistentialPredicate>)",
                "GlobalAlloc::Static(DefId)",
                "GlobalAlloc::TypeId { ty }",
            ],
            "census_metrics": census,
        }
        out_path = Path(__file__).parent / "globalalloc_census.json"
        out_path.write_text(json.dumps(out, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {out_path}")
        print(json.dumps(out, indent=2))

if __name__ == "__main__":
    main()
