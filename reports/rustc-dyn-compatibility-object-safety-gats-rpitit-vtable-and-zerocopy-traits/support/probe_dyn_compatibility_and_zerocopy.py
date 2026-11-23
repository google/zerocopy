#!/usr/bin/env python3
"""Reproducible live rustc probes for dyn-compatibility, vtable layout,
smart-pointer receivers, fn(self) E0161 vs E0038, and google/zerocopy traits.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import subprocess
import tempfile
from pathlib import Path
from typing import Any


def find_zerocopy_lib(explicit: str | None) -> Path | None:
    if explicit:
        p = Path(explicit)
        if p.is_file():
            return p
        cand = p / "zerocopy" / "src" / "lib.rs"
        if cand.is_file():
            return cand
        cand2 = p / "src" / "lib.rs"
        if cand2.is_file():
            return cand2
        return None
    env_root = os.environ.get("ZEROCOPY_ROOT")
    if env_root:
        return find_zerocopy_lib(env_root)
    return None


def read_cargo_pkg_version(zc_lib: Path) -> str:
    cargo_toml = zc_lib.parents[1] / "Cargo.toml"
    if cargo_toml.is_file():
        m = re.search(r'^version\s*=\s*"([^"]+)"', cargo_toml.read_text(encoding="utf-8"), re.M)
        if m:
            return m.group(1)
    return "0.8.0"


def run_rustc_probe(
    tmpdir: Path,
    sysroot: str,
    name: str,
    code: str,
    *,
    edition: str = "2024",
    crate_type: str = "bin",
    extra_args: list[str] | None = None,
    externs: list[tuple[str, Path]] | None = None,
    remap_prefixes: list[tuple[str, str]] | None = None,
    execute: bool = False,
) -> dict[str, Any]:
    src = tmpdir / f"{name}.rs"
    out = tmpdir / (f"lib{name}.rlib" if crate_type == "lib" else f"{name}_bin")
    src.write_text(code, encoding="utf-8")

    cmd = [
        "rustc",
        f"--edition={edition}",
        f"--crate-type={crate_type}",
        f"--remap-path-prefix={tmpdir}=.",
        f"--remap-path-prefix={sysroot}=/rustc-sysroot",
    ]
    for src_prefix, dst_prefix in (remap_prefixes or []):
        cmd.append(f"--remap-path-prefix={src_prefix}={dst_prefix}")
    for ext_name, ext_path in (externs or []):
        cmd.extend(["--extern", f"{ext_name}={ext_path}"])
    if extra_args:
        cmd.extend(extra_args)
    cmd.extend(["-o", str(out), src.name])

    comp = subprocess.run(cmd, cwd=tmpdir, text=True, capture_output=True, check=False)
    stderr = comp.stderr.replace(src.name, "probe.rs")
    result: dict[str, Any] = {
        "name": name,
        "edition": edition,
        "crate_type": crate_type,
        "extra_args": extra_args or [],
        "compile_returncode": comp.returncode,
        "compile_stdout": comp.stdout,
        "compile_stderr": stderr.strip(),
        "error_codes": sorted(set(re.findall(r"error\[(E\d{4})\]", stderr))),
    }
    if execute and comp.returncode == 0 and out.exists():
        run = subprocess.run([str(out)], cwd=tmpdir, text=True, capture_output=True, check=False)
        result["run_returncode"] = run.returncode
        result["run_stdout"] = run.stdout.strip()
        result["run_stderr"] = run.stderr.strip()
    return result


def inspect_vtable_ir(tmpdir: Path, sysroot: str) -> dict[str, Any]:
    code = r"""
use std::rc::Rc;

pub trait SlotProbe {
    fn m1(&self) -> u32;
    fn m_sized(&self) -> u32 where Self: Sized;
    fn m_send(&self) -> u32 where Self: Send;
    fn m_by_val(self) -> u32;
    fn m2(&self) -> u32;
}

impl SlotProbe for u32 {
    fn m1(&self) -> u32 { *self + 1 }
    fn m_sized(&self) -> u32 { *self + 2 }
    fn m_send(&self) -> u32 { *self + 3 }
    fn m_by_val(self) -> u32 { self + 4 }
    fn m2(&self) -> u32 { *self + 5 }
}

impl SlotProbe for Rc<u32> {
    fn m1(&self) -> u32 { **self + 10 }
    fn m_sized(&self) -> u32 { **self + 20 }
    fn m_send(&self) -> u32 { unreachable!() }
    fn m_by_val(self) -> u32 { *self + 40 }
    fn m2(&self) -> u32 { **self + 50 }
}

#[unsafe(no_mangle)]
pub fn make_u32_dyn(x: &u32) -> &dyn SlotProbe {
    x
}

#[unsafe(no_mangle)]
pub fn make_rc_dyn(x: &Rc<u32>) -> &dyn SlotProbe {
    x
}

#[unsafe(no_mangle)]
pub fn call_dyn_methods(d: &dyn SlotProbe) -> u32 {
    d.m1() + d.m2()
}
"""
    src = tmpdir / "vtable_ir.rs"
    ll = tmpdir / "vtable_ir.ll"
    src.write_text(code, encoding="utf-8")
    cmd = [
        "rustc",
        "--edition=2024",
        "--crate-type=lib",
        "-C", "opt-level=0",
        "--emit=llvm-ir",
        f"--remap-path-prefix={tmpdir}=.",
        f"--remap-path-prefix={sysroot}=/rustc-sysroot",
        "-o", str(ll),
        str(src),
    ]
    comp = subprocess.run(cmd, cwd=tmpdir, text=True, capture_output=True, check=False)
    ir_text = ll.read_text(encoding="utf-8") if ll.exists() else ""
    vtables: list[dict[str, Any]] = []
    for line in ir_text.splitlines():
        if "@vtable." in line and " = private unnamed_addr constant " in line:
            m = re.search(r"<\s*\{(.*)\}\s*>", line)
            slots_raw = m.group(1).strip() if m else ""
            # Split the initializer struct (second <{ ... }>) cleanly
            parts = line.split("> <{")
            init_body = parts[1].rsplit("}>", 1)[0].strip() if len(parts) == 2 else slots_raw
            slots = [s.strip() for s in init_body.split(",")] if init_body else []
            vtables.append({
                "global_def": line.strip(),
                "slot_count": len(slots),
                "slots": slots,
            })
    return {
        "compile_returncode": comp.returncode,
        "compile_stderr": comp.stderr.strip(),
        "vtable_count": len(vtables),
        "vtables": vtables,
    }


def build_probes() -> list[tuple[str, str, str, list[str], bool]]:
    """Return list of (group, name, code, extra_args, execute)."""
    return [
        # --- Group A: E0038 violation matrix and Self: Sized exemptions ---
        ("a_violations", "i_sized_self_supertrait_e0038", """
trait NeedsSized: Sized {
    fn ping(&self) -> u32;
}
pub fn use_dyn(_x: &dyn NeedsSized) {}
fn main() {}
""", [], False),
        ("a_violations", "i_sized_self_where_e0038", """
trait NeedsSizedWhere where Self: Sized {
    fn ping(&self) -> u32;
}
pub fn use_dyn(_x: &dyn NeedsSizedWhere) {}
fn main() {}
""", [], False),
        ("a_violations", "i_supertrait_self_type_arg_e0038", """
trait Super<T> {}
trait Bad: Super<Self> {}
pub fn use_dyn(_x: &dyn Bad) {}
fn main() {}
""", [], False),
        ("a_violations", "i_supertrait_self_proj_input_e0038", """
trait Sup<T> { fn id(&self) -> u32; }
trait Bad: Sup<Self::Out> { type Out; }
pub fn use_dyn(_x: &dyn Bad<Out = u32>) {}
fn main() {}
""", [], False),
        ("a_violations", "i_supertrait_self_proj_output_ok", """
trait Sup { type Item; fn get(&self) -> Self::Item; }
trait Sub: Sup<Item = Self::Out> { type Out; }
struct S(u32);
impl Sup for S { type Item = u32; fn get(&self) -> u32 { self.0 } }
impl Sub for S { type Out = u32; }
fn call(x: &dyn Sub<Out = u32, Item = u32>) -> u32 { x.get() }
fn main() {
    let s = S(17);
    println!("SUPERTRAIT_PROJ_OUT={}", call(&s));
}
""", [], True),
        ("a_violations", "ii_generic_method_e0038", """
trait HasGeneric {
    fn foo<T>(&self, x: T);
}
pub fn use_dyn(_x: &dyn HasGeneric) {}
fn main() {}
""", [], False),
        ("a_violations", "ii_generic_method_where_self_sized_ok", """
trait HasGenericExempt {
    fn foo<T>(&self, x: T) -> T where Self: Sized;
    fn dyn_ok(&self) -> u32;
}
struct S(u32);
impl HasGenericExempt for S {
    fn foo<T>(&self, x: T) -> T { x }
    fn dyn_ok(&self) -> u32 { self.0 }
}
fn main() {
    let s = S(42);
    let d: &dyn HasGenericExempt = &s;
    println!("SIZED_EXEMPT_OK={} DYN_OK={}", s.foo(7), d.dyn_ok());
}
""", [], True),
        ("a_violations", "ii_generic_method_where_self_sized_dyn_call_rejected", """
trait HasGenericExempt {
    fn foo<T>(&self, x: T) -> T where Self: Sized;
    fn dyn_ok(&self) -> u32;
}
pub fn call_on_dyn(d: &dyn HasGenericExempt) -> u32 {
    d.foo(7u32)
}
fn main() {}
""", [], False),
        ("a_violations", "iii_static_method_e0038", """
trait HasStatic {
    fn make() -> u32;
}
pub fn use_dyn(_x: &dyn HasStatic) {}
fn main() {}
""", [], False),
        ("a_violations", "iii_static_method_where_self_sized_ok", """
trait HasStaticExempt {
    fn make() -> u32 where Self: Sized;
    fn read(&self) -> u32;
}
struct S(u32);
impl HasStaticExempt for S {
    fn make() -> u32 { 11 }
    fn read(&self) -> u32 { self.0 }
}
fn main() {
    let s = S(S::make());
    let d: &dyn HasStaticExempt = &s;
    println!("STATIC_EXEMPT_OK={}", d.read());
}
""", [], True),
        ("a_violations", "iv_self_input_output_e0038", """
trait SelfInOut {
    fn take(&self, other: Self);
    fn make(&self) -> Self;
}
pub fn use_dyn(_x: &dyn SelfInOut) {}
fn main() {}
""", [], False),
        ("a_violations", "v_by_val_self_allowed_in_dyn_box_call_e0161", """
trait ByVal {
    fn by_val(self) -> u32;
}
struct S(u32);
impl ByVal for S {
    fn by_val(self) -> u32 { self.0 }
}
pub fn call_box(b: Box<dyn ByVal>) -> u32 {
    b.by_val()
}
fn main() {}
""", [], False),
        ("a_violations", "v_by_val_self_allowed_in_dyn_ref_call_e0161_e0507", """
trait ByVal {
    fn by_val(self) -> u32;
}
pub fn call_ref(r: &dyn ByVal) -> u32 {
    r.by_val()
}
fn main() {}
""", [], False),
        ("a_violations", "v_by_val_self_allowed_in_dyn_unused_ok", """
trait ByVal {
    fn by_val(self) -> u32;
    fn peek(&self) -> u32;
}
struct S(u32);
impl ByVal for S {
    fn by_val(self) -> u32 { self.0 + 1 }
    fn peek(&self) -> u32 { self.0 }
}
fn main() {
    let b: Box<dyn ByVal> = Box::new(S(41));
    println!("BY_VAL_TYPE_ALLOWED_PEEK={}", b.peek());
}
""", [], True),
        ("a_violations", "v_by_val_where_self_sized_call_rejected", """
trait ByValExempt {
    fn by_val(self) -> u32 where Self: Sized;
    fn peek(&self) -> u32;
}
pub fn call_box(b: Box<dyn ByValExempt>) -> u32 {
    b.by_val()
}
fn main() {}
""", [], False),
        ("a_violations", "v_by_val_unsized_fn_params_nightly_ok", """
#![feature(unsized_fn_params)]
trait ByVal {
    fn by_val(self) -> u32;
}
struct S(u32);
impl ByVal for S {
    fn by_val(self) -> u32 { self.0 + 5 }
}
fn main() {
    let b: Box<dyn ByVal> = Box::new(S(37));
    println!("UNSIZED_FN_PARAMS_OK={}", b.by_val());
}
""", [], True),
        ("a_violations", "v_box_dyn_fnonce_stable_ok", """
fn main() {
    let x = String::from("fnonce_ok");
    let f: Box<dyn FnOnce() -> usize> = Box::new(move || x.len());
    println!("BOX_DYN_FNONCE_LEN={}", f());
}
""", [], True),
        ("a_violations", "vi_assoc_const_e0038", """
trait HasConst {
    const C: usize;
    fn ping(&self) -> usize;
}
pub fn use_dyn(_x: &dyn HasConst) {}
fn main() {}
""", [], False),
        ("a_violations", "vi_assoc_const_where_self_sized_e0658", """
trait HasConstSized {
    const C: usize where Self: Sized;
    fn ping(&self) -> usize;
}
pub fn use_dyn(_x: &dyn HasConstSized) {}
fn main() {}
""", [], False),
        ("a_violations", "vi_assoc_const_nightly_generic_const_items_self_sized_ok", """
#![feature(generic_const_items)]
trait HasConstSized {
    const C: usize where Self: Sized;
    fn ping(&self) -> usize;
}
struct S(usize);
impl HasConstSized for S {
    const C: usize = 99;
    fn ping(&self) -> usize { self.0 }
}
fn main() {
    let s = S(S::C);
    let d: &dyn HasConstSized = &s;
    println!("GENERIC_CONST_ITEMS_SELF_SIZED_OK={}", d.ping());
}
""", [], True),
        ("a_violations", "vii_assoc_ty_non_gat_missing_e0191", """
trait HasAssoc {
    type Out;
    fn get(&self) -> Self::Out;
}
pub fn missing(_x: &dyn HasAssoc) {}
fn main() {}
""", [], False),
        ("a_violations", "vii_assoc_ty_non_gat_specified_ok", """
trait HasAssoc {
    type Out;
    fn get(&self) -> Self::Out;
}
struct S(u32);
impl HasAssoc for S {
    type Out = u32;
    fn get(&self) -> u32 { self.0 }
}
fn main() {
    let s = S(123);
    let d: &dyn HasAssoc<Out = u32> = &s;
    println!("ASSOC_TY_OK={}", d.get());
}
""", [], True),
        ("a_violations", "vii_gat_e0038", """
trait HasGat {
    type Item<'a> where Self: 'a;
    fn borrow<'a>(&'a self) -> Self::Item<'a>;
}
pub fn use_dyn<'b>(_x: &dyn HasGat<Item<'b> = &'b u32>) {}
fn main() {}
""", [], False),
        ("a_violations", "vii_gat_where_self_sized_ok", """
trait HasGatSized {
    type Item<'a> where Self: 'a + Sized;
    fn borrow<'a>(&'a self) -> Self::Item<'a> where Self: Sized;
    fn tag(&self) -> u32;
}
struct S(u32);
impl HasGatSized for S {
    type Item<'a> = &'a u32;
    fn borrow<'a>(&'a self) -> &'a u32 { &self.0 }
    fn tag(&self) -> u32 { self.0 }
}
fn main() {
    let s = S(55);
    let d: &dyn HasGatSized = &s;
    println!("GAT_EXEMPT_TAG={} CONCRETE_BORROW={}", d.tag(), s.borrow());
}
""", [], True),
        ("a_violations", "vii_gat_where_self_sized_unused_bound_lint", """
trait HasGatSized {
    type Item<'a> where Self: Sized;
    fn tag(&self) -> u32;
}
struct S(u32);
impl HasGatSized for S {
    type Item<'a> = u32;
    fn tag(&self) -> u32 { self.0 }
}
pub fn use_dyn(d: &dyn HasGatSized<Item<'static> = u32>) -> u32 {
    d.tag()
}
fn main() {}
""", [], False),
        ("a_violations", "viii_rpitit_and_async_fn_e0038", """
trait HasRpitit {
    fn make(&self) -> impl core::fmt::Debug;
}
trait HasAsync {
    async fn run(&self) -> u32;
}
pub fn use_rpitit(_x: &dyn HasRpitit) {}
pub fn use_async(_x: &dyn HasAsync) {}
fn main() {}
""", [], False),
        ("a_violations", "viii_rpitit_and_async_fn_where_self_sized_ok", """
trait HasRpititExempt {
    fn make(&self) -> impl core::fmt::Debug where Self: Sized;
    fn id(&self) -> u32;
}
trait HasAsyncExempt {
    async fn run(&self) -> u32 where Self: Sized;
    fn id(&self) -> u32;
}
struct S(u32);
impl HasRpititExempt for S {
    fn make(&self) -> impl core::fmt::Debug { self.0 }
    fn id(&self) -> u32 { self.0 }
}
impl HasAsyncExempt for S {
    async fn run(&self) -> u32 { self.0 }
    fn id(&self) -> u32 { self.0 }
}
fn main() {
    let s = S(88);
    let r: &dyn HasRpititExempt = &s;
    let a: &dyn HasAsyncExempt = &s;
    println!("RPITIT_EXEMPT={} ASYNC_EXEMPT={}", r.id(), a.id());
}
""", [], True),
        ("a_violations", "ix_where_self_clone_elaborates_to_sized_ok", """
trait WhereClone {
    fn f(&self) -> u32 where Self: Clone;
    fn tag(&self) -> u32;
}
struct S(u32);
impl Clone for S { fn clone(&self) -> Self { S(self.0) } }
impl WhereClone for S {
    fn f(&self) -> u32 { self.0 + 1 }
    fn tag(&self) -> u32 { self.0 }
}
fn main() {
    let s = S(30);
    let d: &dyn WhereClone = &s;
    println!("CLONE_ELAB_SIZED_TAG={} CONCRETE_F={}", d.tag(), s.f());
}
""", [], True),
        ("a_violations", "ix_where_self_clone_dyn_call_rejected", """
trait WhereClone {
    fn f(&self) -> u32 where Self: Clone;
}
pub fn call(d: &dyn WhereClone) -> u32 {
    d.f()
}
fn main() {}
""", [], False),
        ("a_violations", "ix_where_self_non_auto_unsized_e0038", """
trait NonAuto {}
trait WhereNonAutoUnsized {
    fn f(&self) -> u32 where Self: NonAuto;
}
pub fn use_dyn(_x: &dyn WhereNonAutoUnsized) {}
fn main() {}
""", [], False),
        ("a_violations", "ix_where_self_static_and_auto_ok", """
trait WhereOk {
    fn f_static(&self) -> u32 where Self: 'static;
    fn f_send(&self) -> u32 where Self: Send;
    fn f_plain(&self) -> u32;
}
struct S(u32);
impl WhereOk for S {
    fn f_static(&self) -> u32 { self.0 + 1 }
    fn f_send(&self) -> u32 { self.0 + 2 }
    fn f_plain(&self) -> u32 { self.0 }
}
fn main() {
    let s = S(10);
    let d_plain: &dyn WhereOk = &s;
    let d_send_static: &(dyn WhereOk + Send + 'static) = &s;
    let rc = std::rc::Rc::new(S(20));
    let d_rc: &dyn WhereOk = &*rc;
    println!("PLAIN={} SEND={} STATIC={} RC_PLAIN={}",
        d_plain.f_plain(), d_send_static.f_send(), d_send_static.f_static(), d_rc.f_plain());
}
""", [], True),
        ("a_violations", "ix_where_self_send_called_without_send_e0277", """
trait WhereSend {
    fn f_send(&self) -> u32 where Self: Send;
}
pub fn call(d: &dyn WhereSend) -> u32 {
    d.f_send()
}
fn main() {}
""", [], False),
        ("a_violations", "x_async_fn_traits_stable_e0038_vs_e0191", """
use std::ops::{AsyncFn, AsyncFnMut, AsyncFnOnce};
pub fn f1(_x: &dyn AsyncFn() -> u32) {}
pub fn f2(_x: &dyn AsyncFnMut() -> u32) {}
pub fn f3(_x: &dyn AsyncFnOnce() -> u32) {}
fn main() {}
""", [], False),
        ("a_violations", "x_box_dyn_async_fn_once_nightly_ok", """
#![feature(async_fn_traits, unboxed_closures)]
use std::future::{Future, Ready, ready};
use std::ops::AsyncFnOnce;
use std::pin::pin;
use std::task::{Context, Poll, Waker};

fn poll_once<F: Future>(f: F) -> F::Output {
    let mut f = pin!(f);
    let waker = Waker::noop();
    let mut cx = Context::from_waker(&waker);
    match f.as_mut().poll(&mut cx) {
        Poll::Ready(v) => v,
        Poll::Pending => panic!("unexpected pending"),
    }
}

fn main() {
    let f: Box<dyn AsyncFnOnce<(), Output = u32, CallOnceFuture = Ready<u32>>> =
        Box::new(|| ready(64u32));
    println!("BOX_DYN_ASYNC_FN_ONCE={}", poll_once(f()));
}
""", [], True),
        # --- Group B: Smart pointer dyn receivers & DispatchFromDyn ---
        ("b_receivers", "valid_std_dyn_receivers", """
use std::pin::Pin;
use std::rc::Rc;
use std::sync::Arc;

trait Receivers {
    fn by_ref(&self) -> u32;
    fn by_mut(&mut self, delta: u32) -> u32;
    fn by_box(self: Box<Self>) -> u32;
    fn by_rc(self: Rc<Self>) -> u32;
    fn by_arc(self: Arc<Self>) -> u32;
    fn by_pin_ref(self: Pin<&Self>) -> u32;
    fn by_pin_mut(self: Pin<&mut Self>) -> u32;
    fn by_pin_box(self: Pin<Box<Self>>) -> u32;
    fn by_pin_rc(self: Pin<Rc<Self>>) -> u32;
    fn by_pin_arc(self: Pin<Arc<Self>>) -> u32;
}

struct Val(u32);
impl Receivers for Val {
    fn by_ref(&self) -> u32 { self.0 }
    fn by_mut(&mut self, delta: u32) -> u32 { self.0 += delta; self.0 }
    fn by_box(self: Box<Self>) -> u32 { self.0 }
    fn by_rc(self: Rc<Self>) -> u32 { self.0 }
    fn by_arc(self: Arc<Self>) -> u32 { self.0 }
    fn by_pin_ref(self: Pin<&Self>) -> u32 { self.0 }
    fn by_pin_mut(self: Pin<&mut Self>) -> u32 { self.0 }
    fn by_pin_box(self: Pin<Box<Self>>) -> u32 { self.0 }
    fn by_pin_rc(self: Pin<Rc<Self>>) -> u32 { self.0 }
    fn by_pin_arc(self: Pin<Arc<Self>>) -> u32 { self.0 }
}

fn main() {
    let mut v = Val(40);
    let r: &dyn Receivers = &v;
    let a = r.by_ref();
    let mr: &mut dyn Receivers = &mut v;
    let b = mr.by_mut(2);
    let bx: Box<dyn Receivers> = Box::new(Val(42));
    let c = bx.by_box();
    let rc: Rc<dyn Receivers> = Rc::new(Val(43));
    let d = rc.by_rc();
    let arc: Arc<dyn Receivers> = Arc::new(Val(44));
    let e = arc.by_arc();
    let pr: Pin<&dyn Receivers> = Pin::new(&v) as Pin<&Val>;
    let f = pr.by_pin_ref();
    let pm: Pin<&mut dyn Receivers> = Pin::new(&mut v) as Pin<&mut Val>;
    let g = pm.by_pin_mut();
    let pb: Pin<Box<dyn Receivers>> = Box::pin(Val(45));
    let h = pb.by_pin_box();
    let prc: Pin<Rc<dyn Receivers>> = Rc::pin(Val(46));
    let i = prc.by_pin_rc();
    let parc: Pin<Arc<dyn Receivers>> = Arc::pin(Val(47));
    let j = parc.by_pin_arc();
    println!("REF={a} MUT={b} BOX={c} RC={d} ARC={e} PIN_REF={f} PIN_MUT={g} PIN_BOX={h} PIN_RC={i} PIN_ARC={j}");
}
""", [], True),
        ("b_receivers", "undispatchable_double_indirection_e0038", """
use std::rc::Rc;
trait BadRecv {
    fn dbl_ref(self: &&Self) -> u32;
    fn rc_box(self: Rc<Box<Self>>) -> u32;
}
pub fn use_dyn(_x: &dyn BadRecv) {}
fn main() {}
""", [], False),
        ("b_receivers", "raw_ptr_receiver_stable_e0658", """
trait RawRecv {
    fn raw(self: *const Self) -> usize;
}
pub fn use_dyn(_x: &dyn RawRecv) {}
fn main() {}
""", [], False),
        ("b_receivers", "raw_ptr_receiver_nightly_arbitrary_ok", """
#![feature(arbitrary_self_types_pointers)]
trait RawRecv {
    fn raw(self: *const Self) -> u32;
}
struct S(u32);
impl RawRecv for S {
    fn raw(self: *const Self) -> u32 { unsafe { (*self).0 } }
}
fn main() {
    let s = S(99);
    let p: *const dyn RawRecv = &s;
    println!("RAW_PTR_DYN={}", p.raw());
}
""", [], True),
        ("b_receivers", "custom_dispatch_from_dyn_wrapper_nightly_ok", """
#![feature(coerce_unsized, dispatch_from_dyn, unsize, arbitrary_self_types)]
use std::marker::Unsize;
use std::ops::{CoerceUnsized, Deref, DispatchFromDyn};

#[repr(transparent)]
struct MyPtr<T: ?Sized>(*const T);

impl<T: ?Sized + Unsize<U>, U: ?Sized> CoerceUnsized<MyPtr<U>> for MyPtr<T> {}
impl<T: ?Sized + Unsize<U>, U: ?Sized> DispatchFromDyn<MyPtr<U>> for MyPtr<T> {}
impl<T: ?Sized> Deref for MyPtr<T> {
    type Target = T;
    fn deref(&self) -> &T { unsafe { &*self.0 } }
}

trait CustomDyn {
    fn get(self: MyPtr<Self>) -> u32;
}
struct S(u32);
impl CustomDyn for S {
    fn get(self: MyPtr<Self>) -> u32 { unsafe { (*self.0).0 } }
}
fn main() {
    let s = S(77);
    let p: MyPtr<dyn CustomDyn> = MyPtr(&s as *const S);
    println!("CUSTOM_DISPATCH_FROM_DYN={}", p.get());
}
""", [], True),
    ]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--zerocopy-root", default=None, help="Path to google/zerocopy repo or zerocopy/src/lib.rs")
    parser.add_argument("--out", default=None, help="Output JSON path (default: probe_results.json next to script)")
    args = parser.parse_args()

    out_path = Path(args.out) if args.out else Path(__file__).resolve().parent / "probe_results.json"
    zc_lib = find_zerocopy_lib(args.zerocopy_root)

    rustc_ver = subprocess.run(["rustc", "--version", "--verbose"], text=True, capture_output=True, check=True).stdout.strip()
    sysroot = subprocess.run(["rustc", "--print", "sysroot"], text=True, capture_output=True, check=True).stdout.strip()

    results: dict[str, Any] = {
        "rustc_version": rustc_ver,
        "groups": {
            "a_violations": {},
            "b_receivers": {},
            "c_vtable_ir": {},
            "d_zerocopy_traits": {},
        },
    }

    with tempfile.TemporaryDirectory() as tmp:
        tmpdir = Path(tmp)
        for group, name, code, extra_args, execute in build_probes():
            results["groups"][group][name] = run_rustc_probe(
                tmpdir, sysroot, name, code, extra_args=extra_args, execute=execute
            )

        results["groups"]["c_vtable_ir"] = inspect_vtable_ir(tmpdir, sysroot)

        if zc_lib is not None:
            zc_repo_root = zc_lib.parents[2]
            zc_ver = read_cargo_pkg_version(zc_lib)
            zc_rlib = tmpdir / "libzerocopy.rlib"
            zc_cmd = [
                "rustc",
                "--edition=2021",
                "--crate-name=zerocopy",
                "--crate-type=lib",
                f"--remap-path-prefix={zc_repo_root}=google/zerocopy",
                f"--remap-path-prefix={sysroot}=/rustc-sysroot",
                "-o", str(zc_rlib),
                str(zc_lib),
            ]
            zc_env = {**os.environ, "CARGO_PKG_VERSION": zc_ver}
            zc_comp = subprocess.run(zc_cmd, cwd=tmpdir, env=zc_env, text=True, capture_output=True, check=False)
            results["groups"]["d_zerocopy_traits"]["zerocopy_compile"] = {
                "edition": "2021",
                "cargo_pkg_version": zc_ver,
                "features": [],
                "compile_returncode": zc_comp.returncode,
                "compile_stderr": zc_comp.stderr.strip(),
            }
            if zc_comp.returncode == 0:
                zc_probes = [
                    ("Immutable_dyn_ok", """
use zerocopy::Immutable;
struct MyVal(u32);
unsafe impl Immutable for MyVal {
    fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
}
fn inspect(x: &dyn Immutable) -> usize { core::mem::size_of_val(x) }
fn main() {
    let v = MyVal(42);
    let d: &dyn Immutable = &v;
    println!("ZC_IMMUTABLE_DYN_OK=1 SIZE={}", inspect(d));
}
""", True),
                    ("Unaligned_dyn_ok", """
use zerocopy::Unaligned;
struct MyByte(u8);
unsafe impl Unaligned for MyByte {
    fn only_derive_is_allowed_to_implement_this_trait() where Self: Sized {}
}
fn inspect(x: &dyn Unaligned) -> usize { core::mem::size_of_val(x) }
fn main() {
    let v = MyByte(7);
    let d: &dyn Unaligned = &v;
    println!("ZC_UNALIGNED_DYN_OK=1 SIZE={}", inspect(d));
}
""", True),
                    ("KnownLayout_e0038", """
use zerocopy::KnownLayout;
pub fn f(_x: &dyn KnownLayout<PointerMetadata = (), MaybeUninit = u32>) {}
fn main() {}
""", False),
                    ("TryFromBytes_e0038", """
use zerocopy::TryFromBytes;
pub fn f(_x: &dyn TryFromBytes) {}
fn main() {}
""", False),
                    ("FromZeros_e0038", """
use zerocopy::FromZeros;
pub fn f(_x: &dyn FromZeros) {}
fn main() {}
""", False),
                    ("FromBytes_e0038", """
use zerocopy::FromBytes;
pub fn f(_x: &dyn FromBytes) {}
fn main() {}
""", False),
                    ("IntoBytes_e0038", """
use zerocopy::IntoBytes;
pub fn f(_x: &dyn IntoBytes) {}
fn main() {}
""", False),
                ]
                for zname, zcode, zexec in zc_probes:
                    results["groups"]["d_zerocopy_traits"][zname] = run_rustc_probe(
                        tmpdir,
                        sysroot,
                        f"zc_{zname}",
                        zcode,
                        edition="2024",
                        externs=[("zerocopy", zc_rlib)],
                        remap_prefixes=[(str(zc_repo_root), "google/zerocopy")],
                        execute=zexec,
                    )
        else:
            results["groups"]["d_zerocopy_traits"]["skipped"] = (
                "No --zerocopy-root or ZEROCOPY_ROOT provided; pass --zerocopy-root to run zerocopy trait probes."
            )

    out_path.write_text(json.dumps(results, indent=2) + "\n", encoding="utf-8")
    print(f"wrote {out_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
