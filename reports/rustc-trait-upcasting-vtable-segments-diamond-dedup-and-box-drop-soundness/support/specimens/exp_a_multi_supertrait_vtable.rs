#![allow(dead_code)]

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
