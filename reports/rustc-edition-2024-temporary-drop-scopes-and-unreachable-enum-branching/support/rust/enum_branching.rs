//! `UnreachableEnumBranching` and discriminant reads of an uninhabited variant.
//!
//! `Tri` is `#[repr(u8)]`, so its layout is a `u8` tag at offset 0 followed by
//! the variant payload (`A`'s `u32` at offset 4). Variant `B` is uninhabited
//! because its payload type `Never` has no values.
//!
//! cfg flags select which forged tag `main` feeds to which function:
//!   (none)                valid tags 0 and 2 only
//!   --cfg tag1_place      tag 1 (uninhabited `B`) into `classify_raw_wildcard`
//!   --cfg tag1_value      tag 1 into `classify_raw_value`
//!   --cfg tag3_place      tag 3 (no such variant) into `classify_raw_wildcard`

use std::mem::MaybeUninit;

#[derive(Clone, Copy)]
pub enum Never {}

#[derive(Clone, Copy)]
#[repr(u8)]
pub enum Tri {
    A(u32),
    B(Never),
    C,
}

/// Place scrutinee: only the discriminant of `*p` is read before branching.
#[inline(never)]
pub fn classify_raw_wildcard(p: *const Tri) -> u32 {
    unsafe {
        match *p {
            Tri::A(v) => v + 1,
            _ => 77,
        }
    }
}

/// Block (value) scrutinee: `*p` is first copied into a temporary.
#[inline(never)]
pub fn classify_raw_value(p: *const Tri) -> u32 {
    match unsafe { *p } {
        Tri::A(v) => v + 1,
        _ => 77,
    }
}

/// Every variant named, through a reference.
#[inline(never)]
pub fn classify_ref(t: &Tri) -> u32 {
    match *t {
        Tri::A(v) => v + 1,
        Tri::B(n) => match n {},
        Tri::C => 77,
    }
}

/// Writes `tag` into the tag byte and `payload` into `A`'s payload slot.
#[inline(never)]
fn forge(tag: u8, payload: u32) -> MaybeUninit<Tri> {
    let mut slot = MaybeUninit::<Tri>::uninit();
    unsafe {
        let base = slot.as_mut_ptr() as *mut u8;
        (base.add(4) as *mut u32).write(payload);
        base.write(tag);
    }
    slot
}

fn main() {
    assert_eq!(std::mem::size_of::<Tri>(), 8);
    let a = forge(0, 41);
    let c = forge(2, 0);
    println!(
        "VALID A={} C={} A_VALUE={} C_VALUE={} A_REF={} C_REF={}",
        classify_raw_wildcard(a.as_ptr()),
        classify_raw_wildcard(c.as_ptr()),
        classify_raw_value(a.as_ptr()),
        classify_raw_value(c.as_ptr()),
        classify_ref(&Tri::A(41)),
        classify_ref(&Tri::C),
    );
    #[cfg(tag1_place)]
    {
        let b = forge(1, 41);
        println!("TAG1_PLACE={}", classify_raw_wildcard(b.as_ptr()));
    }
    #[cfg(tag1_value)]
    {
        let b = forge(1, 41);
        println!("TAG1_VALUE={}", classify_raw_value(b.as_ptr()));
    }
    #[cfg(tag3_place)]
    {
        let d = forge(3, 41);
        println!("TAG3_PLACE={}", classify_raw_wildcard(d.as_ptr()));
    }
}
