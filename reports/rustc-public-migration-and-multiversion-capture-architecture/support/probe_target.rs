#![crate_type = "lib"]
#![feature(ergonomic_clones)]
#![allow(dead_code, unused_variables, incomplete_features)]

use core::num::NonZeroU8;

#[repr(C)]
pub struct ReprCStruct {
    pub a: u8,
    pub b: u32,
    pub c: u8,
}

#[repr(C, packed(2))]
pub struct PackedStruct {
    pub x: u8,
    pub y: u64,
}

#[repr(align(16))]
pub struct AlignedStruct(pub u8);

#[repr(transparent)]
pub struct TransparentWrapper(pub u32, ());

pub struct ReprRustStruct {
    pub x: u8,
    pub y: u64,
    pub z: u16,
}

#[repr(u16)]
pub enum ExplicitDiscrEnum {
    First = 10,
    Second = 42,
}

pub enum NicheEnum {
    EmptyA,
    WithNz(NonZeroU8),
    EmptyB,
}

pub enum MultiVariant {
    A(u32),
    B { lo: u8, hi: u16 },
}

pub enum Uninhabited {}

#[repr(C)]
pub union RawUnion {
    pub byte: u8,
    pub word: u32,
}

pub struct GenericStruct<T>(pub T, pub u8);

pub const C_U32: u32 = 12345;
pub const C_ZST: () = ();
pub static S_VAL: u64 = 0xdeadbeef_cafebabe;
pub static S_REF: &u64 = &S_VAL;
pub const SLICE_CONST: &[u8] = &[1, 2, 3, 4];

pub unsafe fn raw_ptr_deref_and_ub(p: *const u32) -> u32 {
    unsafe { *p }
}

pub fn checked_overflow_fn(a: u32, b: u32) -> u32 {
    a + b
}

pub fn place_mention_test(x: &ReprCStruct) -> u8 {
    let _ = x.c;
    x.a
}

pub fn generic_id<T: Copy>(v: T) -> T {
    v
}

#[inline(always)]
#[cold]
pub fn attr_fn(x: u32) -> u32 {
    generic_id(x)
}

pub fn const_eval_fn() -> usize {
    let arr = [0u8; 2 + 2];
    arr.len() + (*S_REF as usize) + (C_U32 as usize) + SLICE_CONST.len()
}

pub fn niche_match(v: NicheEnum) -> u8 {
    match v {
        NicheEnum::EmptyA => 1,
        NicheEnum::WithNz(n) => n.get(),
        NicheEnum::EmptyB => 2,
    }
}

pub fn call_fn_ptr(f: fn(u32) -> u32, x: u32) -> u32 {
    f(x)
}

pub fn fn_ptr_const() -> fn(u32) -> u32 {
    attr_fn
}

pub unsafe fn inline_asm_fn(x: u64) -> u64 {
    let out: u64;
    unsafe {
        core::arch::asm!(
            "mov {out}, {inp}",
            inp = in(reg) x,
            out = lateout(reg) out,
            options(nomem, nostack, preserves_flags),
        );
    }
    out
}

pub fn touch_all_adts(
    a: ReprCStruct,
    b: PackedStruct,
    c: AlignedStruct,
    d: TransparentWrapper,
    e: ReprRustStruct,
    f: ExplicitDiscrEnum,
    g: MultiVariant,
    h: GenericStruct<u16>,
    u: Option<Uninhabited>,
    nz_opt: Option<NonZeroU8>,
    ref_opt: Option<&'static u8>,
) -> usize {
    core::mem::size_of_val(&a)
        + core::mem::size_of_val(&b)
        + core::mem::size_of_val(&c)
        + core::mem::size_of_val(&d)
        + core::mem::size_of_val(&e)
        + core::mem::size_of_val(&f)
        + core::mem::size_of_val(&g)
        + core::mem::size_of_val(&h)
        + core::mem::size_of_val(&u)
        + core::mem::size_of_val(&nz_opt)
        + core::mem::size_of_val(&ref_opt)
}

core::arch::global_asm!(".text");

pub fn generic_ctfe_bomb<T>() -> usize {
    struct Bomb<T>(core::marker::PhantomData<T>);
    impl<T> Bomb<T> {
        const BOOM: usize = if core::mem::size_of::<T>() == 1 {
            panic!("ctfe post-mono fail on 1-byte T")
        } else {
            42
        };
    }
    Bomb::<T>::BOOM
}

pub fn call_ctfe_ok() -> usize {
    generic_ctfe_bomb::<u32>()
}

pub fn union_uninit_const() -> RawUnion {
    const U_VAL: RawUnion = RawUnion { byte: 7 };
    U_VAL
}

pub fn cleanup_unwind_test(b: bool) -> u32 {
    struct DropGuard;
    impl Drop for DropGuard {
        fn drop(&mut self) {}
    }
    let _g = DropGuard;
    if b {
        panic!("boom");
    }
    7
}

pub fn ergonomic_use_fn(x: RcLike) -> RcLike {
    x.use
}

pub struct RcLike(pub u8);
impl Clone for RcLike {
    fn clone(&self) -> Self {
        RcLike(self.0)
    }
}
impl core::clone::UseCloned for RcLike {}
