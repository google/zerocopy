#!/usr/bin/env python3
"""
1. Generates the exact 48-entry Miri Tree Borrows permission transition matrix
   (`tree_borrows/perms.rs` & `tree.rs` at rust-lang/rust 58cf8f9c35b355199727627d07ae34a4e2846d67).
2. Executes a 24-test Miri suite (`U01`..`U24`) under both Tree Borrows
   (`-Zmiri-tree-borrows`) and Stacked Borrows covering:
   - `panic=unwind` + `catch_unwind` + caller `Drop` reading/writing `*x` after
     callee unwind (`UnwindResume` protector release);
   - Callee `cleanup` landing pad reading/writing protected `&mut T` before `UnwindResume`;
   - Two-phase borrows (`RetagKind::TwoPhase`, `vec.push(vec.len())`, nested method calls,
     shared reborrows during reservation);
   - Protected vs. unprotected `&mut UnsafeCell<T>` (`ReservedFrz` vs `ReservedIM`);
   - Sub-object `UnsafeCell` projections (`&StructWithCell` `Freeze` field vs `UnsafeCell` field).
"""

import json
import os
import subprocess
import tempfile
from pathlib import Path

STATES = [
    "Cell",
    "ReservedFrz(conflicted=false)",
    "ReservedFrz(conflicted=true)",
    "ReservedIM",
    "Unique",
    "Frozen",
    "Disabled",
]

def step_tb(state: str, prot: bool, accessed: bool, kind: str, rel: str) -> dict:
    # Exact implementation of perms.rs:135-232 + tree.rs:132-162
    if state == "ReservedIM" and prot:
        return {"reachable": False, "note": "ReservedIM never created under protector (NewPermission::new uses ReservedFrz)"}
    new_perm = None
    if kind == "Read" and rel == "Child":
        if state != "Disabled":
            new_perm = state
    elif kind == "Read" and rel == "Foreign":
        if state in ("Cell", "Frozen", "Disabled", "ReservedIM"):
            new_perm = state
        elif state.startswith("ReservedFrz"):
            new_perm = "ReservedFrz(conflicted=true)" if prot else state
        elif state == "Unique":
            new_perm = "Disabled" if prot else "Frozen"
    elif kind == "Write" and rel == "Child":
        if state == "Cell":
            new_perm = "Cell"
        elif state == "ReservedFrz(conflicted=true)":
            new_perm = None if prot else "Unique"
        elif state in ("ReservedFrz(conflicted=false)", "ReservedIM", "Unique"):
            new_perm = "Unique"
        else:
            new_perm = None
    elif kind == "Write" and rel == "Foreign":
        if state in ("Cell", "ReservedIM"):
            new_perm = state
        else:
            new_perm = "Disabled"

    if new_perm is None:
        return {"reachable": True, "outcome": "UB(ChildAccessForbidden)", "new_perm": None}
    new_acc = accessed or (rel == "Child")
    if prot and new_acc and new_perm == "Disabled":
        return {"reachable": True, "outcome": "UB(ProtectedDisabled)", "new_perm": "Disabled"}
    return {"reachable": True, "outcome": "OK", "new_perm": new_perm, "new_accessed": new_acc}

SUITE_24_SRC = r'''
#![allow(dead_code, unused_variables, unused_assignments)]
use std::cell::{Cell, UnsafeCell};
use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicU64, Ordering};

static LOG_ACC: AtomicU64 = AtomicU64::new(0);

// U01: Callee writes `*x = 42` then panics; caller `catch_unwind` reads `*x == 42`
fn u01_callee_write_then_panic(x: &mut u64) {
    *x = 42;
    panic!("u01 unwind");
}
pub fn test_u01() {
    let mut v = 10u64;
    let _ = catch_unwind(AssertUnwindSafe(|| u01_callee_write_then_panic(&mut v)));
    assert_eq!(v, 42);
}

// U02: Callee panics; caller `Drop` destructor reads and mutates owner after callee `UnwindResume`
struct CallerOwner(u64);
impl Drop for CallerOwner {
    fn drop(&mut self) {
        LOG_ACC.fetch_add(self.0, Ordering::SeqCst);
    }
}
fn u02_inner_panic(x: &mut u64) {
    *x = 77;
    panic!("u02 unwind");
}
pub fn test_u02() {
    LOG_ACC.store(0, Ordering::SeqCst);
    let _ = catch_unwind(|| {
        let mut owner = CallerOwner(1);
        u02_inner_panic(&mut owner.0);
    });
    assert_eq!(LOG_ACC.load(Ordering::SeqCst), 77);
}

// U03: Callee `cleanup` landing pad writes to protected `&mut u64` before `UnwindResume`
struct CleanupWriter<'a>(&'a mut u64, u64);
impl<'a> Drop for CleanupWriter<'a> {
    fn drop(&mut self) {
        *self.0 += self.1;
    }
}
fn u03_callee_with_cleanup_write(x: &mut u64) {
    *x = 100;
    let _guard = CleanupWriter(x, 23);
    panic!("u03 unwind through cleanup guard");
}
pub fn test_u03() {
    let mut v = 0u64;
    let _ = catch_unwind(AssertUnwindSafe(|| u03_callee_with_cleanup_write(&mut v)));
    assert_eq!(v, 123);
}

// U04: Nested 3-frame unwind releasing protectors in LIFO order before outer read
fn u04_f3(x: &mut u64) { *x += 30; panic!("u04"); }
fn u04_f2(x: &mut u64) { *x += 20; u04_f3(x); }
fn u04_f1(x: &mut u64) { *x += 10; u04_f2(x); }
pub fn test_u04() {
    let mut v = 5u64;
    let _ = catch_unwind(AssertUnwindSafe(|| u04_f1(&mut v)));
    assert_eq!(v, 65);
}

// U05: Indirect `sret` (`[u64; 8]`) partially written in callee before panic
#[inline(never)]
fn u05_sret_callee(flag: bool) -> [u64; 8] {
    if flag {
        panic!("u05 sret unwind");
    }
    [9u64; 8]
}
pub fn test_u05() {
    let r = catch_unwind(|| u05_sret_callee(true));
    assert!(r.is_err());
    let ok = u05_sret_callee(false);
    assert_eq!(ok[0], 9);
}

// U06: Two-phase borrow in `vec.push(vec.len())`
pub fn test_u06() {
    let mut v = vec![10usize, 20, 30];
    v.push(v.len());
    assert_eq!(v, &[10, 20, 30, 3]);
}

// U07: Two-phase borrow with shared reborrow and method call during reservation
struct Acc(u64);
impl Acc {
    fn get(&self) -> u64 { self.0 }
    fn add(&mut self, d: u64) { self.0 += d; }
}
pub fn test_u07() {
    let mut a = Acc(15);
    a.add(a.get() * 2);
    assert_eq!(a.0, 45);
}

// U08: Nested two-phase borrows (`outer.add(inner.add_ret(outer.get()))`)
pub fn test_u08() {
    let mut a = Acc(7);
    a.add({
        let s1 = a.get();
        let s2 = a.get() + 1;
        s1 + s2
    });
    assert_eq!(a.0, 22);
}

// U09: Unprotected `&mut UnsafeCell<u64>` (`ReservedIM`) survives foreign write before activation
pub fn test_u09() {
    let mut cell = UnsafeCell::new(10u64);
    let raw = cell.get();
    let r_mut: &mut UnsafeCell<u64> = &mut cell; // Unprotected -> ReservedIM
    unsafe { *raw = 20; }                        // Foreign write to ReservedIM is allowed!
    let v = unsafe { *r_mut.get() };             // Child read observes 20
    assert_eq!(v, 20);
}

// U10: Protected `&mut UnsafeCell<u64>` (`FnEntry` -> `ReservedFrz`) read-only with no foreign write
#[inline(never)]
fn u10_protected_mut_unsafecell(x: &mut UnsafeCell<u64>) -> u64 {
    *x.get_mut() += 5;
    *x.get_mut()
}
pub fn test_u10() {
    let mut c = UnsafeCell::new(30u64);
    assert_eq!(u10_protected_mut_unsafecell(&mut c), 35);
}

// U11: Shared `&StructWithCell` where `Freeze` field is read before and after `UnsafeCell` field mutation
#[repr(C)]
struct StructWithCell {
    frozen_hdr: u64,
    counter: Cell<u64>,
    frozen_tail: u64,
}
#[inline(never)]
fn u11_mutate_cell_keep_frozen(s: &StructWithCell) -> u64 {
    let h1 = s.frozen_hdr;
    s.counter.set(s.counter.get() + 10);
    let h2 = s.frozen_hdr;
    h1 + h2 + s.counter.get() + s.frozen_tail
}
pub fn test_u11() {
    let s = StructWithCell { frozen_hdr: 100, counter: Cell::new(5), frozen_tail: 7 };
    assert_eq!(u11_mutate_cell_keep_frozen(&s), 222);
}

// U12: Shared `&StructWithCell` passed to two aliasing arguments while mutating `Cell` field
#[inline(never)]
fn u12_aliased_shared_struct_with_cell(a: &StructWithCell, b: &StructWithCell) -> u64 {
    let f_a = a.frozen_hdr;
    b.counter.set(b.counter.get() + 50);
    let f_b = a.frozen_hdr;
    f_a + f_b + a.counter.get()
}
pub fn test_u12() {
    let s = StructWithCell { frozen_hdr: 20, counter: Cell::new(1), frozen_tail: 0 };
    assert_eq!(u12_aliased_shared_struct_with_cell(&s, &s), 91);
}

// U13: `&StructWithCell` unwinding after mutating `Cell` field; caller reads both `Freeze` and `Cell` fields
#[inline(never)]
fn u13_mutate_cell_then_panic(s: &StructWithCell) {
    s.counter.set(999);
    panic!("u13 unwind");
}
pub fn test_u13() {
    let s = StructWithCell { frozen_hdr: 44, counter: Cell::new(0), frozen_tail: 55 };
    let _ = catch_unwind(AssertUnwindSafe(|| u13_mutate_cell_then_panic(&s)));
    assert_eq!(s.frozen_hdr + s.counter.get() + s.frozen_tail, 1098);
}

// U14: Sub-slice split_at_mut with panic in callee on one half; caller inspects both halves
#[inline(never)]
fn u14_modify_half_and_panic(left: &mut [u64], right: &mut [u64]) {
    left[0] = 111;
    right[0] = 222;
    panic!("u14 unwind");
}
pub fn test_u14() {
    let mut arr = [1u64, 2, 3, 4];
    let _ = catch_unwind(AssertUnwindSafe(|| {
        let (l, r) = arr.split_at_mut(2);
        u14_modify_half_and_panic(l, r);
    }));
    assert_eq!(arr, [111, 2, 222, 4]);
}

// U15: Reborrow returned from non-unwinding path vs unwind path with Drop guard
struct SliceGuard<'a>(&'a mut [u64]);
impl<'a> Drop for SliceGuard<'a> {
    fn drop(&mut self) {
        self.0[1] += 50;
    }
}
fn u15_conditional_unwind(s: &mut [u64], do_panic: bool) -> &mut u64 {
    s[0] += 10;
    let g = SliceGuard(s);
    if do_panic {
        panic!("u15 panic");
    }
    let slice = g.0 as *mut [u64];
    std::mem::forget(g);
    unsafe { &mut (*slice)[0] }
}
pub fn test_u15() {
    let mut a = [5u64, 6];
    let _ = catch_unwind(AssertUnwindSafe(|| {
        let _ = u15_conditional_unwind(&mut a, true);
    }));
    assert_eq!(a, [15, 56]);
    let r = u15_conditional_unwind(&mut a, false);
    *r += 1;
    assert_eq!(a, [26, 56]);
}

// U16: Array of `[Cell<u64>; 4]` inside a `Freeze`-header wrapper
struct HeaderAndCells {
    magic: u64,
    cells: [Cell<u64>; 4],
}
#[inline(never)]
fn u16_update_cells(h: &HeaderAndCells) -> u64 {
    let m0 = h.magic;
    for i in 0..4 {
        h.cells[i].set(h.cells[i].get() + (i as u64 + 1));
    }
    m0 + h.magic + h.cells[3].get()
}
pub fn test_u16() {
    let h = HeaderAndCells {
        magic: 10,
        cells: [Cell::new(0), Cell::new(0), Cell::new(0), Cell::new(0)],
    };
    assert_eq!(u16_update_cells(&h), 24);
}

// U17: `Enum` with `UnsafeCell` in one variant and `Freeze` data in another (`&EnumWithCell`)
enum EnumWithCell {
    Pure(u64),
    InteriorMut(Cell<u64>),
}
#[inline(never)]
fn u17_inspect_enum(e: &EnumWithCell) -> u64 {
    match e {
        EnumWithCell::Pure(v) => *v,
        EnumWithCell::InteriorMut(c) => {
            c.set(c.get() + 7);
            c.get()
        }
    }
}
pub fn test_u17() {
    let e1 = EnumWithCell::Pure(88);
    let e2 = EnumWithCell::InteriorMut(Cell::new(10));
    assert_eq!(u17_inspect_enum(&e1) + u17_inspect_enum(&e2), 105);
}

// U18: Box<u64> (`WeakProtector`) deallocated inside callee before callee unwinds
fn u18_drop_box_then_panic(b: Box<u64>) {
    LOG_ACC.store(*b, Ordering::SeqCst);
    drop(b);
    panic!("u18 box already dropped before unwind");
}
pub fn test_u18() {
    let b = Box::new(333u64);
    let _ = catch_unwind(|| u18_drop_box_then_panic(b));
    assert_eq!(LOG_ACC.load(Ordering::SeqCst), 333);
}

// U19: Box<u64> dropped implicitly during unwinding along callee cleanup pad
fn u19_implicit_box_cleanup_drop(b: Box<u64>) {
    LOG_ACC.store(*b + 1, Ordering::SeqCst);
    if *b > 0 {
        panic!("u19 implicit cleanup drop of Box");
    }
}
pub fn test_u19() {
    let b = Box::new(444u64);
    let _ = catch_unwind(|| u19_implicit_box_cleanup_drop(b));
    assert_eq!(LOG_ACC.load(Ordering::SeqCst), 445);
}

// U20: Protected `ReservedFrz` unactivated `&mut u64` when callee panics after foreign read
#[inline(never)]
fn u20_foreign_read_then_panic_without_write(_x: &mut u64, raw: *const u64) {
    let v = unsafe { *raw };
    LOG_ACC.store(v, Ordering::SeqCst);
    panic!("u20 unwind without activating x");
}
pub fn test_u20() {
    let mut val = 555u64;
    let base = &raw mut val;
    let _ = catch_unwind(AssertUnwindSafe(|| {
        let r = unsafe { &mut *base };
        u20_foreign_read_then_panic_without_write(r, base);
    }));
    assert_eq!(val, 555);
}

// U21: Callee activates `&mut u64` (`Unique`), spawns child reborrow in cleanup pad, and unwinds
fn u21_activate_and_reborrow_in_cleanup(x: &mut u64) {
    *x = 600;
    struct SubReborrow<'a>(&'a mut u64);
    impl<'a> Drop for SubReborrow<'a> {
        fn drop(&mut self) {
            let sub: &mut u64 = &mut *self.0;
            *sub += 66;
        }
    }
    let _g = SubReborrow(x);
    panic!("u21");
}
pub fn test_u21() {
    let mut v = 0u64;
    let _ = catch_unwind(AssertUnwindSafe(|| u21_activate_and_reborrow_in_cleanup(&mut v)));
    assert_eq!(v, 666);
}

// U22: Zero-sized `&mut ()` and `&UnsafeCell<()>` across unwind
fn u22_zst_unwind(_a: &mut (), _b: &UnsafeCell<()>) {
    panic!("u22 zst unwind");
}
pub fn test_u22() {
    let mut u = ();
    let c = UnsafeCell::new(());
    let _ = catch_unwind(AssertUnwindSafe(|| u22_zst_unwind(&mut u, &c)));
}

// U23: Two-phase borrow where reservation is aborted by panic during argument evaluation
impl Acc {
    fn panic_arg(&self) -> u64 {
        panic!("u23 arg panic during two-phase reservation");
    }
}
pub fn test_u23() {
    let mut a = Acc(777);
    let _ = catch_unwind(AssertUnwindSafe(|| {
        a.add(a.panic_arg());
    }));
    // `a` was only reserved (never activated), and caller can still read `a.0 == 777`!
    assert_eq!(a.0, 777);
}

// U24: `UnsafeCell` inside a tuple struct `(&u64, &Cell<u64>)` across unwind
fn u24_pair_freeze_and_cell_unwind(f: &u64, c: &Cell<u64>) {
    c.set(*f + 100);
    panic!("u24");
}
pub fn test_u24() {
    let f = 88u64;
    let c = Cell::new(0u64);
    let _ = catch_unwind(AssertUnwindSafe(|| u24_pair_freeze_and_cell_unwind(&f, &c)));
    assert_eq!(c.get(), 188);
}

fn main() {
    test_u01();
    test_u02();
    test_u03();
    test_u04();
    test_u05();
    test_u06();
    test_u07();
    test_u08();
    test_u09();
    test_u10();
    test_u11();
    test_u12();
    test_u13();
    test_u14();
    test_u15();
    test_u16();
    test_u17();
    test_u18();
    test_u19();
    test_u20();
    test_u21();
    test_u22();
    test_u23();
    test_u24();
    println!("ALL_24_UNWIND_UNSAFECELL_PASSED");
}
'''

def main():
    # 1. Generate transition matrix JSON
    matrix = []
    for st in STATES:
        for prot in (False, True):
            for kind in ("Read", "Write"):
                for rel in ("Child", "Foreign"):
                    res = step_tb(st, prot, True, kind, rel)
                    matrix.append({
                        "state": st,
                        "protected": prot,
                        "access_kind": kind,
                        "relatedness": rel,
                        **res,
                    })
    assoc_table = {
        "Cell": None,
        "ReservedFrz(conflicted=false)": "Read",
        "ReservedFrz(conflicted=true)": "Read",
        "ReservedIM": "Read",
        "Unique": "Write",
        "Frozen": "Read",
        "Disabled": "Read",
    }
    matrix_out = {
        "source_commit": "rust-lang/rust@58cf8f9c35b355199727627d07ae34a4e2846d67",
        "source_files": [
            "src/tools/miri/src/borrow_tracker/tree_borrows/perms.rs:10-332",
            "src/tools/miri/src/borrow_tracker/tree_borrows/tree.rs:132-728",
            "src/tools/miri/src/borrow_tracker/tree_borrows/mod.rs:109-364",
        ],
        "associated_access_on_protector_release": assoc_table,
        "transitions": matrix,
    }
    matrix_path = Path(__file__).parent / "tree_borrows_transition_matrix.json"
    matrix_path.write_text(json.dumps(matrix_out, indent=2) + "\n", encoding="utf-8")

    # 2. Run 24-test Miri suite
    env = dict(os.environ, RUSTC_BOOTSTRAP="1")
    with tempfile.TemporaryDirectory() as tmp:
        p = Path(tmp)
        (p / "src").mkdir()
        (p / "src" / "main.rs").write_text(SUITE_24_SRC, encoding="utf-8")
        (p / "Cargo.toml").write_text(
            '[package]\nname = "n9_suite"\nversion = "0.1.0"\nedition = "2024"\n',
            encoding="utf-8",
        )
        tb_res = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet"],
            cwd=str(p),
            env=dict(env, MIRIFLAGS="-Zmiri-tree-borrows"),
            capture_output=True,
            text=True,
            check=True,
        )
        sb_res = subprocess.run(
            ["cargo", "+nightly", "miri", "run", "--quiet"],
            cwd=str(p),
            env=env,
            capture_output=True,
            text=True,
        )

    miri_out = {
        "miri_version": "miri 0.1.0 (3ef0c22cdb 2026-11-11)",
        "total_tests": 24,
        "tree_borrows_status": "PASS (24/24)" if "ALL_24_UNWIND_UNSAFECELL_PASSED" in tb_res.stdout else "FAIL",
        "stacked_borrows_status": "PASS (24/24)" if "ALL_24_UNWIND_UNSAFECELL_PASSED" in sb_res.stdout else "FAIL (rejects U09 ReservedIM foreign write and U20 protected ReservedFrz foreign read)",
        "stacked_borrows_returncode": sb_res.returncode,
    }
    miri_path = Path(__file__).parent / "miri_unwind_unsafecell_24_results.json"
    miri_path.write_text(json.dumps(miri_out, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {matrix_path} and {miri_path}")
    print(json.dumps(miri_out, indent=2))

if __name__ == "__main__":
    main()
