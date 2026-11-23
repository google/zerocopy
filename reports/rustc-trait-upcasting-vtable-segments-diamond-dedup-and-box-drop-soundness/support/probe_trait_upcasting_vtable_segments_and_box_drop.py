#!/usr/bin/env python3
"""Differential compiler, LLVM-IR, MIR, and Miri probe for:
1. Multi-supertrait vtable segments, primary prefix reuse, empty-marker rule,
   3-supertrait TraitVPtr slots, Vacant slots, and nullable slot-0 drop;
2. Diamond supertrait deduplication & path coherence vs. generic ambiguity (E0308);
3. Box<dyn Sub> -> Box<dyn SuperB> (and 3-hop chains, plus !needs_drop)
   ownership, drop order, and deallocation Layout(size, align) soundness.

Uses Python 3.10+ standard library only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any

SPECIMEN_A_SRC = r'''#![allow(dead_code)]

use std::mem::{align_of_val, size_of_val};

trait SuperA {
    fn a(&self) -> u64;
}

trait SuperB {
    fn b(&self) -> u64;
}

trait SuperC {
    fn c1(&self) -> u64;
    fn c2(&self) -> u64;
}

trait Sub: SuperA + SuperB {
    fn sub(&self) -> u64;
}

trait Tri: SuperA + SuperB + SuperC {
    fn tri(&self) -> u64;
}

trait EmptyMarker {}

trait SubAfterEmpty: EmptyMarker + SuperB {
    fn sub_e(&self) -> u64;
}

trait CondVacant<T> {
    fn always(&self) -> u64;
    fn only_copy(&self) -> u64
    where
        T: Copy;
}

#[repr(C, align(16))]
struct Impl {
    v: u64,
}

impl SuperA for Impl {
    #[inline(never)]
    fn a(&self) -> u64 {
        self.v + 10
    }
}

impl SuperB for Impl {
    #[inline(never)]
    fn b(&self) -> u64 {
        self.v + 20
    }
}

impl SuperC for Impl {
    #[inline(never)]
    fn c1(&self) -> u64 {
        self.v + 31
    }
    #[inline(never)]
    fn c2(&self) -> u64 {
        self.v + 32
    }
}

impl Sub for Impl {
    #[inline(never)]
    fn sub(&self) -> u64 {
        self.v + 100
    }
}

impl Tri for Impl {
    #[inline(never)]
    fn tri(&self) -> u64 {
        self.v + 200
    }
}

impl EmptyMarker for Impl {}

impl SubAfterEmpty for Impl {
    #[inline(never)]
    fn sub_e(&self) -> u64 {
        self.v + 300
    }
}

struct NonCopy(String);

impl<T> CondVacant<T> for Impl {
    #[inline(never)]
    fn always(&self) -> u64 {
        self.v + 400
    }
    fn only_copy(&self) -> u64
    where
        T: Copy,
    {
        unreachable!()
    }
}

#[inline(never)]
fn upcast_to_a(r: &dyn Sub) -> &dyn SuperA {
    r
}

#[inline(never)]
fn upcast_to_b(r: &dyn Sub) -> &dyn SuperB {
    r
}

#[inline(never)]
fn upcast_after_empty_to_b(r: &dyn SubAfterEmpty) -> &dyn SuperB {
    r
}

#[inline(never)]
fn upcast_tri_to_a(r: &dyn Tri) -> &dyn SuperA {
    r
}

#[inline(never)]
fn upcast_tri_to_b(r: &dyn Tri) -> &dyn SuperB {
    r
}

#[inline(never)]
fn upcast_tri_to_c(r: &dyn Tri) -> &dyn SuperC {
    r
}

#[inline(never)]
fn make_vacant_dyn(r: &Impl) -> &dyn CondVacant<NonCopy> {
    r
}

#[inline(never)]
unsafe fn raw_parts_addr<T: ?Sized>(r: &T) -> (usize, usize) {
    assert_eq!(std::mem::size_of::<&T>(), std::mem::size_of::<(usize, usize)>());
    // SAFETY: wide pointer representation of `&dyn Trait` on 64-bit is `(data_ptr, vtable_ptr)`.
    unsafe { std::mem::transmute_copy::<&T, (usize, usize)>(&r) }
}

fn main() {
    let x = std::hint::black_box(Impl { v: 7 });
    let r_sub: &dyn Sub = std::hint::black_box(&x);
    let r_a: &dyn SuperA = upcast_to_a(r_sub);
    let r_b: &dyn SuperB = upcast_to_b(r_sub);
    let r_direct_b: &dyn SuperB = std::hint::black_box(&x);

    let r_ae: &dyn SubAfterEmpty = std::hint::black_box(&x);
    let r_ae_b: &dyn SuperB = upcast_after_empty_to_b(r_ae);

    let r_tri: &dyn Tri = std::hint::black_box(&x);
    let r_tri_a: &dyn SuperA = upcast_tri_to_a(r_tri);
    let r_tri_b: &dyn SuperB = upcast_tri_to_b(r_tri);
    let r_tri_c: &dyn SuperC = upcast_tri_to_c(r_tri);

    let r_vac = make_vacant_dyn(&x);

    let (d_sub, v_sub) = unsafe { raw_parts_addr(r_sub) };
    let (d_a, v_a) = unsafe { raw_parts_addr(r_a) };
    let (d_b, v_b) = unsafe { raw_parts_addr(r_b) };
    let (_, v_direct_b) = unsafe { raw_parts_addr(r_direct_b) };
    let (_, v_ae) = unsafe { raw_parts_addr(r_ae) };
    let (_, v_ae_b) = unsafe { raw_parts_addr(r_ae_b) };
    let (_, v_tri) = unsafe { raw_parts_addr(r_tri) };
    let (_, v_tri_a) = unsafe { raw_parts_addr(r_tri_a) };
    let (_, v_tri_b) = unsafe { raw_parts_addr(r_tri_b) };
    let (_, v_tri_c) = unsafe { raw_parts_addr(r_tri_c) };

    println!(
        "SUB_DATA_EQ_A={} SUB_DATA_EQ_B={}",
        d_sub == d_a,
        d_sub == d_b
    );
    println!(
        "VPTR_SUB_EQ_A={} VPTR_SUB_EQ_B={} VPTR_B_EQ_DIRECT_B={}",
        v_sub == v_a,
        v_sub == v_b,
        v_b == v_direct_b
    );
    println!("VPTR_AFTER_EMPTY_EQ_B={}", v_ae == v_ae_b);
    println!(
        "VPTR_TRI_EQ_A={} VPTR_TRI_EQ_B={} VPTR_TRI_EQ_C={}",
        v_tri == v_tri_a,
        v_tri == v_tri_b,
        v_tri == v_tri_c
    );
    println!(
        "SIZES={},{},{} ALIGNS={},{},{}",
        size_of_val(r_sub),
        size_of_val(r_a),
        size_of_val(r_b),
        align_of_val(r_sub),
        align_of_val(r_a),
        align_of_val(r_b)
    );
    println!(
        "CALLS={},{},{},{},{},{},{}",
        r_a.a(),
        r_b.b(),
        r_sub.sub(),
        r_ae_b.b(),
        r_tri_b.b(),
        r_tri_c.c2(),
        r_vac.always()
    );
}
'''

SPECIMEN_B_SRC = r'''#![allow(dead_code)]

trait Root {
    fn root(&self) -> u64;
}

trait Sibling {
    fn sib(&self) -> u64;
}

trait Left: Root {
    fn left(&self) -> u64;
}

trait Right: Root {
    fn right(&self) -> u64;
}

trait Diamond: Left + Right {
    fn dia(&self) -> u64;
}

// Non-primary Right path: Sibling first, Root second.
trait RightSecond: Sibling + Root {
    fn rsec(&self) -> u64;
}

trait DiamondAsym: Left + RightSecond {
    fn dia2(&self) -> u64;
}

trait GenRoot<T> {
    fn tag(&self) -> u64;
}

trait AmbigDia: GenRoot<u8> + GenRoot<u16> {
    fn ambig(&self) -> u64;
}

struct Node(u64);

impl Root for Node {
    #[inline(never)]
    fn root(&self) -> u64 {
        self.0 + 1
    }
}

impl Sibling for Node {
    #[inline(never)]
    fn sib(&self) -> u64 {
        self.0 + 5
    }
}

impl Left for Node {
    #[inline(never)]
    fn left(&self) -> u64 {
        self.0 + 2
    }
}

impl Right for Node {
    #[inline(never)]
    fn right(&self) -> u64 {
        self.0 + 3
    }
}

impl Diamond for Node {
    #[inline(never)]
    fn dia(&self) -> u64 {
        self.0 + 4
    }
}

impl RightSecond for Node {
    #[inline(never)]
    fn rsec(&self) -> u64 {
        self.0 + 6
    }
}

impl DiamondAsym for Node {
    #[inline(never)]
    fn dia2(&self) -> u64 {
        self.0 + 7
    }
}

impl GenRoot<u8> for Node {
    #[inline(never)]
    fn tag(&self) -> u64 {
        8
    }
}

impl GenRoot<u16> for Node {
    #[inline(never)]
    fn tag(&self) -> u64 {
        16
    }
}

impl AmbigDia for Node {
    #[inline(never)]
    fn ambig(&self) -> u64 {
        self.0 + 9
    }
}

#[inline(never)]
fn dia_to_left(d: &dyn Diamond) -> &dyn Left {
    d
}

#[inline(never)]
fn dia_to_right(d: &dyn Diamond) -> &dyn Right {
    d
}

#[inline(never)]
fn dia_to_root(d: &dyn Diamond) -> &dyn Root {
    d
}

#[inline(never)]
fn left_to_root(l: &dyn Left) -> &dyn Root {
    l
}

#[inline(never)]
fn right_to_root(r: &dyn Right) -> &dyn Root {
    r
}

#[inline(never)]
fn asym_to_right_second(d: &dyn DiamondAsym) -> &dyn RightSecond {
    d
}

#[inline(never)]
fn asym_to_root(d: &dyn DiamondAsym) -> &dyn Root {
    d
}

#[inline(never)]
fn right_second_to_root(r: &dyn RightSecond) -> &dyn Root {
    r
}

#[inline(never)]
fn ambig_to_u8(d: &dyn AmbigDia) -> &dyn GenRoot<u8> {
    d
}

#[inline(never)]
fn ambig_to_u16(d: &dyn AmbigDia) -> &dyn GenRoot<u16> {
    d
}

#[inline(never)]
unsafe fn vptr_addr<T: ?Sized>(r: &T) -> usize {
    assert_eq!(std::mem::size_of::<&T>(), std::mem::size_of::<(usize, usize)>());
    unsafe { std::mem::transmute_copy::<&T, (usize, usize)>(&r).1 }
}

fn main() {
    let n = std::hint::black_box(Node(100));
    let d: &dyn Diamond = std::hint::black_box(&n);
    let l = dia_to_left(d);
    let r = dia_to_right(d);
    let root_from_d = dia_to_root(d);
    let root_from_l = left_to_root(l);
    let root_from_r = right_to_root(r);
    let r_direct: &dyn Right = std::hint::black_box(&n);
    let root_direct: &dyn Root = std::hint::black_box(&n);

    let vd = unsafe { vptr_addr(d) };
    let vl = unsafe { vptr_addr(l) };
    let vr = unsafe { vptr_addr(r) };
    let vr_dir = unsafe { vptr_addr(r_direct) };
    let vroot_d = unsafe { vptr_addr(root_from_d) };
    let vroot_l = unsafe { vptr_addr(root_from_l) };
    let vroot_r = unsafe { vptr_addr(root_from_r) };
    let vroot_dir = unsafe { vptr_addr(root_direct) };

    println!(
        "D_EQ_L={} L_EQ_ROOT={} D_EQ_ROOT_FROM_D={} R_EQ_RDIR={} ROOT_FROM_R_EQ_DIR={}",
        vd == vl,
        vl == vroot_l,
        vd == vroot_d,
        vr == vr_dir,
        vroot_r == vroot_dir
    );
    println!(
        "D_EQ_R={} ROOT_FROM_D_EQ_ROOT_FROM_R={}",
        vd == vr,
        vroot_d == vroot_r
    );

    let d2: &dyn DiamondAsym = std::hint::black_box(&n);
    let r2 = asym_to_right_second(d2);
    let root_asym_direct = asym_to_root(d2);
    let root_asym_via_r2 = right_second_to_root(r2);
    let vd2 = unsafe { vptr_addr(d2) };
    let vr2 = unsafe { vptr_addr(r2) };
    let vr2_root = unsafe { vptr_addr(root_asym_via_r2) };
    println!(
        "ASYM_D_EQ_ROOT={} ASYM_D_EQ_R2={} ASYM_R2_EQ_ROOT={} ASYM_ROOT_CALLS={},{}",
        vd2 == unsafe { vptr_addr(root_asym_direct) },
        vd2 == vr2,
        vr2 == vr2_root,
        root_asym_direct.root(),
        root_asym_via_r2.root()
    );

    let amb: &dyn AmbigDia = std::hint::black_box(&n);
    let g8 = ambig_to_u8(amb);
    let g16 = ambig_to_u16(amb);

    println!(
        "CALLS={},{},{},{},{},{} GEN_TAGS={},{}",
        d.dia(),
        l.left(),
        r.right(),
        root_from_d.root(),
        root_from_l.root(),
        root_from_r.root(),
        g8.tag(),
        g16.tag()
    );
}
'''

SPECIMEN_B_NEG_AMBIG = r'''#![allow(dead_code)]

trait GenRoot<T> {
    fn tag(&self) -> u64;
}

trait AmbigDia: GenRoot<u8> + GenRoot<u16> {}

fn upcast(d: &dyn AmbigDia) {
    let _x: &dyn GenRoot<_> = d;
}

fn main() {}
'''

SPECIMEN_B_NEG_SAME_INFER = r'''#![allow(dead_code)]

trait GenRoot<T> {
    fn tag(&self) -> u64;
}

trait LeftU8: GenRoot<u8> {}
trait RightU8: GenRoot<u8> {}
trait SameGenDia: LeftU8 + RightU8 {}

fn upcast(d: &dyn SameGenDia) -> u64 {
    let x: &dyn GenRoot<_> = d;
    x.tag()
}

fn main() {}
'''

SPECIMEN_C_SRC = r'''#![allow(dead_code)]

use std::alloc::{GlobalAlloc, Layout, System};
use std::mem::{align_of, align_of_val, size_of, size_of_val};
use std::sync::Mutex;

static LOG: Mutex<Vec<String>> = Mutex::new(Vec::new());
static RECORD_DEALLOC: Mutex<Vec<(usize, usize)>> = Mutex::new(Vec::new());

struct SpyAlloc;

unsafe impl GlobalAlloc for SpyAlloc {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        unsafe { System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        if (layout.size() == 32 || layout.size() == 64) && layout.align() == 32 {
            if let Ok(mut guard) = RECORD_DEALLOC.try_lock() {
                guard.push((layout.size(), layout.align()));
            }
        }
        unsafe { System.dealloc(ptr, layout) }
    }
}

#[global_allocator]
static ALLOC: SpyAlloc = SpyAlloc;

trait SuperA {
    fn id_a(&self) -> u64;
}

trait SuperB {
    fn id_b(&self) -> u64;
}

trait Sub: SuperA + SuperB {
    fn id_sub(&self) -> u64;
}

// 3-hop secondary upcast chain: Tier3 -> Tier2 -> Tier1 -> Tier0
trait Prim0 {
    fn p0(&self) -> u64;
}
trait Prim1 {
    fn p1(&self) -> u64;
}
trait Prim2 {
    fn p2(&self) -> u64;
}
trait Tier0 {
    fn t0(&self) -> u64;
}
trait Tier1: Prim1 + Tier0 {
    fn t1(&self) -> u64;
}
trait Tier2: Prim2 + Tier1 {
    fn t2(&self) -> u64;
}
trait Tier3: Prim0 + Tier2 {
    fn t3(&self) -> u64;
}

struct InnerDrop {
    tag: &'static str,
}

impl Drop for InnerDrop {
    fn drop(&mut self) {
        LOG.lock().unwrap().push(format!("drop_{}", self.tag));
    }
}

#[repr(C, align(32))]
struct DropTracker {
    a: u64,
    b: u64,
    inner: InnerDrop,
}

impl Drop for DropTracker {
    fn drop(&mut self) {
        LOG.lock().unwrap().push("drop_outer".to_string());
    }
}

impl SuperA for DropTracker {
    fn id_a(&self) -> u64 {
        self.a
    }
}
impl SuperB for DropTracker {
    fn id_b(&self) -> u64 {
        self.b
    }
}
impl Sub for DropTracker {
    fn id_sub(&self) -> u64 {
        self.a + self.b
    }
}
impl Prim0 for DropTracker {
    fn p0(&self) -> u64 {
        10
    }
}
impl Prim1 for DropTracker {
    fn p1(&self) -> u64 {
        11
    }
}
impl Prim2 for DropTracker {
    fn p2(&self) -> u64 {
        12
    }
}
impl Tier0 for DropTracker {
    fn t0(&self) -> u64 {
        self.a + 100
    }
}
impl Tier1 for DropTracker {
    fn t1(&self) -> u64 {
        self.a + 101
    }
}
impl Tier2 for DropTracker {
    fn t2(&self) -> u64 {
        self.a + 102
    }
}
impl Tier3 for DropTracker {
    fn t3(&self) -> u64 {
        self.a + 103
    }
}

#[repr(C, align(32))]
struct NoDropBig {
    words: [u64; 8],
}

impl SuperA for NoDropBig {
    fn id_a(&self) -> u64 {
        self.words[0]
    }
}
impl SuperB for NoDropBig {
    fn id_b(&self) -> u64 {
        self.words[1]
    }
}
impl Sub for NoDropBig {
    fn id_sub(&self) -> u64 {
        self.words[0] + self.words[1]
    }
}

#[inline(never)]
fn upcast_box_to_b(b: Box<dyn Sub>) -> Box<dyn SuperB> {
    b
}

#[inline(never)]
fn upcast_chain_3hop(b: Box<dyn Tier3>) -> Box<dyn Tier0> {
    let b2: Box<dyn Tier2> = b;
    let b1: Box<dyn Tier1> = b2;
    let b0: Box<dyn Tier0> = b1;
    b0
}

fn main() {
    let concrete_size = size_of::<DropTracker>();
    let concrete_align = align_of::<DropTracker>();

    let boxed_sub: Box<dyn Sub> = Box::new(DropTracker {
        a: 1,
        b: 2,
        inner: InnerDrop { tag: "inner" },
    });
    let sz_sub = size_of_val(&*boxed_sub);
    let al_sub = align_of_val(&*boxed_sub);

    let boxed_b: Box<dyn SuperB> = upcast_box_to_b(boxed_sub);
    let sz_b = size_of_val(&*boxed_b);
    let al_b = align_of_val(&*boxed_b);
    let val_b = boxed_b.id_b();

    drop(boxed_b);
    LOG.lock().unwrap().push("after_drop".to_string());

    // 3-hop secondary upcast chain
    let boxed_t3: Box<dyn Tier3> = Box::new(DropTracker {
        a: 5,
        b: 6,
        inner: InnerDrop { tag: "inner_3hop" },
    });
    let boxed_t0: Box<dyn Tier0> = upcast_chain_3hop(boxed_t3);
    let sz_t0 = size_of_val(&*boxed_t0);
    let al_t0 = align_of_val(&*boxed_t0);
    let val_t0 = boxed_t0.t0();
    drop(boxed_t0);

    // !needs_drop Box<dyn Sub> -> Box<dyn SuperB>
    let boxed_nodrop: Box<dyn Sub> = Box::new(NoDropBig { words: [11, 22, 0, 0, 0, 0, 0, 0] });
    let boxed_nodrop_b: Box<dyn SuperB> = upcast_box_to_b(boxed_nodrop);
    let sz_nd = size_of_val(&*boxed_nodrop_b);
    let al_nd = align_of_val(&*boxed_nodrop_b);
    let val_nd = boxed_nodrop_b.id_b();
    drop(boxed_nodrop_b);

    let log = LOG.lock().unwrap().clone();
    let deallocs = RECORD_DEALLOC.lock().unwrap().clone();

    println!(
        "CONCRETE=({concrete_size},{concrete_align}) SUB=({sz_sub},{al_sub}) B=({sz_b},{al_b}) T0=({sz_t0},{al_t0}) ND=({sz_nd},{al_nd})"
    );
    println!("VALS={val_b},{val_t0},{val_nd}");
    println!("DROP_ORDER={log:?}");
    println!("DEALLOC_LAYOUTS={deallocs:?}");
}
'''


def sanitize_home(text: str) -> str:
    home_str = str(Path.home())
    if home_str and home_str != "/":
        return text.replace(home_str, "~")
    return text


def run_cmd(cmd: list[str], cwd: Path | None = None, env: dict[str, str] | None = None) -> dict[str, Any]:
    proc = subprocess.run(
        cmd,
        cwd=str(cwd) if cwd else None,
        env=env,
        capture_output=True,
        text=True,
        check=False,
    )
    return {
        "cmd": sanitize_home(" ".join(cmd)),
        "returncode": proc.returncode,
        "stdout": sanitize_home(proc.stdout.strip()),
        "stderr": sanitize_home(proc.stderr.strip()),
    }


def extract_vtables_and_fns(ll_text: str, fn_prefixes: list[str]) -> dict[str, Any]:
    vtables = [
        line.strip()
        for line in ll_text.splitlines()
        if line.startswith("@vtable.") or ("constant" in line and "@alloc_" in line and "ptr @" in line)
    ]
    defs: list[str] = []
    lines = ll_text.splitlines()
    i = 0
    while i < len(lines):
        line = lines[i]
        if line.startswith("define ") and any(p in line for p in fn_prefixes):
            block = [line]
            i += 1
            while i < len(lines):
                block.append(lines[i])
                if lines[i].strip() == "}":
                    break
                i += 1
            defs.append("\n".join(block))
        i += 1
    return {"vtables": vtables, "defined_functions": defs}


def run_miri_crate(name: str, src: str, flags: list[str] | None = None) -> dict[str, Any]:
    with tempfile.TemporaryDirectory(prefix=f"miri_{name}_") as td:
        root = Path(td)
        (root / "src").mkdir()
        (root / "Cargo.toml").write_text(
            f'[package]\nname = "{name}"\nversion = "0.1.0"\nedition = "2021"\n',
            encoding="utf-8",
        )
        (root / "src" / "main.rs").write_text(src, encoding="utf-8")
        env = os.environ.copy()
        if flags:
            env["MIRIFLAGS"] = " ".join(flags)
        res = run_cmd(["cargo", "miri", "run"], cwd=root, env=env)
        res["miriflags"] = " ".join(flags) if flags else "<default Stacked Borrows>"
        return res


def compile_and_probe_single(
    work: Path,
    name: str,
    src_path: Path,
    fn_prefixes: list[str],
    llvm_excerpts: list[str],
    mir_excerpts: list[str],
) -> dict[str, Any]:
    res: dict[str, Any] = {}
    for opt in ("0", "2"):
        bin_path = work / f"{name}_O{opt}"
        ll_path = work / f"{name}_O{opt}.ll"
        c_bin = run_cmd(
            ["rustc", "--edition=2021", "-C", f"opt-level={opt}", "-C", "debuginfo=0", str(src_path), "-o", str(bin_path)]
        )
        c_ll = run_cmd(
            ["rustc", "--edition=2021", "-C", f"opt-level={opt}", "-C", "debuginfo=0", "--emit=llvm-ir", str(src_path), "-o", str(ll_path)]
        )
        run_res = run_cmd([str(bin_path)]) if c_bin["returncode"] == 0 else {"returncode": -1, "stdout": "", "stderr": "compile failed"}
        ll_text = ll_path.read_text(encoding="utf-8") if ll_path.exists() else ""
        extracted = extract_vtables_and_fns(ll_text, fn_prefixes)
        llvm_excerpts.append(f"=== {name} (-O{opt}) ===\n" + "\n".join(extracted["vtables"]) + "\n\n" + "\n\n".join(extracted["defined_functions"]) + "\n")
        res[f"opt_{opt}"] = {
            "compile": c_bin,
            "emit_llvm_ir": c_ll,
            "run": run_res,
            "llvm_vtables_count": len(extracted["vtables"]),
            "llvm_vtables": extracted["vtables"],
            "llvm_functions": extracted["defined_functions"],
        }

    # MIR dump for post-cleanup and runtime-optimized
    mir_dir = work / f"mir_{name}"
    mir_dir.mkdir(parents=True, exist_ok=True)
    mir_cmd = run_cmd(
        [
            "rustc",
            "--edition=2021",
            "-C",
            "opt-level=0",
            "-Z",
            "dump-mir=all",
            "-Z",
            f"dump-mir-dir={mir_dir}",
            "--crate-type=bin",
            str(src_path),
            "-o",
            str(work / f"{name}_mir_bin"),
        ]
    )
    mir_files: dict[str, str] = {}
    for p in sorted(mir_dir.glob("*.mir")):
        if any(fn in p.name for fn in fn_prefixes) and (
            "runtime-post-cleanup.after" in p.name or "runtime-optimized.after" in p.name
        ):
            txt = p.read_text(encoding="utf-8")
            mir_files[p.name] = txt
            mir_excerpts.append(f"=== {p.name} ===\n{txt}\n")
    res["mir_dump_returncode"] = mir_cmd["returncode"]
    res["mir_files_captured"] = sorted(mir_files.keys())
    return res


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=None, help="Output directory (default: support/probe_output)")
    args = parser.parse_args()

    support_dir = Path(__file__).resolve().parent
    specimens_dir = support_dir / "specimens"
    out_dir = args.out.resolve() if args.out else (support_dir / "probe_output")
    specimens_dir.mkdir(parents=True, exist_ok=True)
    out_dir.mkdir(parents=True, exist_ok=True)

    spec_a = specimens_dir / "exp_a_multi_supertrait_vtable.rs"
    spec_b = specimens_dir / "exp_b_diamond_upcast.rs"
    spec_b_neg1 = specimens_dir / "exp_b_neg_ambig_infer.rs"
    spec_b_neg2 = specimens_dir / "exp_b_neg_same_infer.rs"
    spec_c = specimens_dir / "exp_c_box_upcast_drop_dealloc.rs"

    spec_a.write_text(SPECIMEN_A_SRC, encoding="utf-8")
    spec_b.write_text(SPECIMEN_B_SRC, encoding="utf-8")
    spec_b_neg1.write_text(SPECIMEN_B_NEG_AMBIG, encoding="utf-8")
    spec_b_neg2.write_text(SPECIMEN_B_NEG_SAME_INFER, encoding="utf-8")
    spec_c.write_text(SPECIMEN_C_SRC, encoding="utf-8")

    rustc_ver = run_cmd(["rustc", "-Vv"])
    miri_ver = run_cmd(["cargo", "miri", "--version"])

    llvm_excerpts: list[str] = []
    mir_excerpts: list[str] = []

    with tempfile.TemporaryDirectory(prefix="probe_upcast_") as td:
        work = Path(td)

        exp_a = compile_and_probe_single(
            work,
            "exp_a",
            spec_a,
            [
                "upcast_to_a",
                "upcast_to_b",
                "upcast_after_empty_to_b",
                "upcast_tri_to_a",
                "upcast_tri_to_b",
                "upcast_tri_to_c",
                "make_vacant_dyn",
            ],
            llvm_excerpts,
            mir_excerpts,
        )
        exp_a["miri_stacked_borrows"] = run_miri_crate("exp_a_miri", SPECIMEN_A_SRC)
        exp_a["miri_tree_borrows"] = run_miri_crate("exp_a_miri_tb", SPECIMEN_A_SRC, ["-Zmiri-tree-borrows"])

        exp_b = compile_and_probe_single(
            work,
            "exp_b",
            spec_b,
            [
                "dia_to_left",
                "dia_to_right",
                "dia_to_root",
                "left_to_root",
                "right_to_root",
                "asym_to_right_second",
                "asym_to_root",
                "right_second_to_root",
                "ambig_to_u8",
                "ambig_to_u16",
            ],
            llvm_excerpts,
            mir_excerpts,
        )
        exp_b["miri_stacked_borrows"] = run_miri_crate("exp_b_miri", SPECIMEN_B_SRC)
        exp_b["miri_tree_borrows"] = run_miri_crate("exp_b_miri_tb", SPECIMEN_B_SRC, ["-Zmiri-tree-borrows"])
        exp_b["negative_ambig_infer"] = run_cmd(
            ["rustc", "--edition=2021", str(spec_b_neg1), "-o", str(work / "neg1")]
        )
        exp_b["negative_same_infer"] = run_cmd(
            ["rustc", "--edition=2021", str(spec_b_neg2), "-o", str(work / "neg2")]
        )

        exp_c = compile_and_probe_single(
            work,
            "exp_c",
            spec_c,
            ["upcast_box_to_b", "upcast_chain_3hop", "drop_glue"],
            llvm_excerpts,
            mir_excerpts,
        )
        exp_c["miri_stacked_borrows"] = run_miri_crate("exp_c_miri", SPECIMEN_C_SRC)
        exp_c["miri_tree_borrows"] = run_miri_crate("exp_c_miri_tb", SPECIMEN_C_SRC, ["-Zmiri-tree-borrows"])

    # Structured discriminating assertions
    a_o2_out = exp_a["opt_2"]["run"]["stdout"]
    a_o0_ir = "\n".join(exp_a["opt_0"]["llvm_functions"])
    a_o0_vt = "\n".join(exp_a["opt_0"]["llvm_vtables"])
    b_o2_out = exp_b["opt_2"]["run"]["stdout"]
    b_o0_ir = "\n".join(exp_b["opt_0"]["llvm_functions"])
    c_o2_out = exp_c["opt_2"]["run"]["stdout"]
    c_o0_ir = "\n".join(exp_c["opt_0"]["llvm_functions"])

    checks: dict[str, bool] = {
        "a::native_o2_prefix_and_secondary_vptr": (
            "SUB_DATA_EQ_A=true SUB_DATA_EQ_B=true" in a_o2_out
            and "VPTR_SUB_EQ_A=true VPTR_SUB_EQ_B=false VPTR_B_EQ_DIRECT_B=true" in a_o2_out
        ),
        "a::empty_marker_preserves_prefix": "VPTR_AFTER_EMPTY_EQ_B=true" in a_o2_out,
        "a::tri_supertrait_prefix_vs_secondary": "VPTR_TRI_EQ_A=true VPTR_TRI_EQ_B=false VPTR_TRI_EQ_C=false" in a_o2_out,
        "a::sizes_aligns_and_calls": (
            "SIZES=16,16,16 ALIGNS=16,16,16" in a_o2_out
            and "CALLS=17,27,107,27,27,39,407" in a_o2_out
        ),
        "a::llvm_o0_upcast_to_b_loads_slot": (
            "upcast_to_b" in a_o0_ir and "getelementptr inbounds i8, ptr %r.1, i64 40" in a_o0_ir and "!invariant.load" in a_o0_ir and "!nonnull" in a_o0_ir
        ),
        "a::llvm_o0_upcast_to_a_and_empty_noop": (
            "upcast_to_a" in a_o0_ir and "upcast_after_empty_to_b" in a_o0_ir
        ),
        "a::llvm_vacant_undef_and_null_drop_header": (
            "undef" in a_o0_vt and "\\00\\00\\00\\00\\00\\00\\00\\00" in a_o0_vt
        ),
        "a::miri_sb_and_tb_pass_and_symbolic_vptr": (
            exp_a["miri_stacked_borrows"]["returncode"] == 0
            and exp_a["miri_tree_borrows"]["returncode"] == 0
            and "VPTR_SUB_EQ_A=false" in exp_a["miri_stacked_borrows"]["stdout"]
            and "VPTR_SUB_EQ_A=false" in exp_a["miri_tree_borrows"]["stdout"]
        ),
        "b::diamond_dedup_native_o2": (
            "D_EQ_L=true L_EQ_ROOT=true D_EQ_ROOT_FROM_D=true R_EQ_RDIR=true ROOT_FROM_R_EQ_DIR=false" in b_o2_out
            and "D_EQ_R=false ROOT_FROM_D_EQ_ROOT_FROM_R=false" in b_o2_out
            and "CALLS=104,102,103,101,101,101 GEN_TAGS=8,16" in b_o2_out
        ),
        "b::diamond_asym_coherent_dispatch": (
            "ASYM_D_EQ_ROOT=true ASYM_D_EQ_R2=false ASYM_R2_EQ_ROOT=false ASYM_ROOT_CALLS=101,101" in b_o2_out
        ),
        "b::diamond_llvm_o0_gep_48": "getelementptr inbounds i8, ptr %d.1, i64 48" in b_o0_ir,
        "b::negative_ambig_infer_e0308": (
            exp_b["negative_ambig_infer"]["returncode"] != 0
            and "error[E0308]" in exp_b["negative_ambig_infer"]["stderr"]
        ),
        "b::same_gen_diamond_infer_accepted": exp_b["negative_same_infer"]["returncode"] == 0,
        "b::miri_sb_and_tb_pass": (
            exp_b["miri_stacked_borrows"]["returncode"] == 0
            and exp_b["miri_tree_borrows"]["returncode"] == 0
        ),
        "c::box_drop_order_and_concrete_dealloc_layout": (
            "CONCRETE=(32,32) SUB=(32,32) B=(32,32) T0=(32,32) ND=(64,32)" in c_o2_out
            and "VALS=2,105,22" in c_o2_out
            and 'DROP_ORDER=["drop_outer", "drop_inner", "after_drop", "drop_outer", "drop_inner_3hop"]' in c_o2_out
            and "DEALLOC_LAYOUTS=[(32, 32), (32, 32), (64, 32)]" in c_o2_out
        ),
        "c::llvm_o0_box_upcast_gep_40_and_null_checked_drop": (
            "getelementptr inbounds i8, ptr %b.1, i64 40" in c_o0_ir
            and "icmp ne ptr" in c_o0_ir
        ),
        "c::miri_sb_and_tb_pass_with_dealloc_layout": (
            exp_c["miri_stacked_borrows"]["returncode"] == 0
            and exp_c["miri_tree_borrows"]["returncode"] == 0
            and "DEALLOC_LAYOUTS=[(32, 32), (32, 32), (64, 32)]" in exp_c["miri_stacked_borrows"]["stdout"]
            and "DEALLOC_LAYOUTS=[(32, 32), (32, 32), (64, 32)]" in exp_c["miri_tree_borrows"]["stdout"]
        ),
    }

    specimen_hashes = {
        p.name: hashlib.sha256(p.read_bytes()).hexdigest()
        for p in (spec_a, spec_b, spec_b_neg1, spec_b_neg2, spec_c)
    }

    payload = {
        "rustc_version": rustc_ver["stdout"],
        "miri_version": miri_ver["stdout"],
        "specimen_sha256": specimen_hashes,
        "checks": checks,
        "passed_count": sum(1 for v in checks.values() if v),
        "total_checks": len(checks),
        "all_passed": all(checks.values()),
        "experiments": {
            "a_multi_supertrait_vtable_segments": exp_a,
            "b_diamond_dedup_and_generic_ambiguity": exp_b,
            "c_box_dyn_upcast_drop_and_dealloc": exp_c,
        },
    }

    (out_dir / "probe_results.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    (out_dir / "llvm_ir_excerpts.txt").write_text("\n".join(llvm_excerpts), encoding="utf-8")
    (out_dir / "mir_excerpts.txt").write_text("\n".join(mir_excerpts), encoding="utf-8")

    print(f"Probe checks: {payload['passed_count']}/{payload['total_checks']} passed")
    for k, v in checks.items():
        if not v:
            print(f"FAILED CHECK: {k}", file=sys.stderr)
    print(f"negative_same_infer rc={exp_b['negative_same_infer']['returncode']}")
    if exp_b["negative_same_infer"]["stderr"]:
        print("negative_same_infer stderr:", exp_b["negative_same_infer"]["stderr"])
    return 0 if payload["all_passed"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
