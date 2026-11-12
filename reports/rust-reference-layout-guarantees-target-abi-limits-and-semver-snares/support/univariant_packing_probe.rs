// Empirical probe: rustc_abi::layout::univariant behavior on Sandwich, InevitablePad,
// TwoU24, nested structs, MaybeUnsized structs/tuples, all-ZST structs, and
// #[repr(transparent)] with ZST siblings.

use std::mem::{align_of, offset_of, size_of};
use std::marker::PhantomData;

#[repr(Rust)]
pub struct Sandwich {
    pub a: u8,
    pub b: u16,
    pub c: u8,
}

#[repr(C)]
pub struct CSandwich {
    pub a: u8,
    pub b: u16,
    pub c: u8,
}

#[repr(Rust)]
pub struct InevitablePad {
    pub a: [u8; 3],
    pub b: u32,
}

#[repr(Rust)]
pub struct TwoU24 {
    pub a: [u8; 3],
    pub b: [u8; 3],
    pub c: u32,
}

#[repr(Rust)]
pub struct Mixed {
    pub a: u8,
    pub b: u64,
}

#[repr(Rust)]
pub struct Pair {
    pub a: u32,
    pub b: u32,
}

#[repr(C)]
pub struct CPair {
    pub a: u32,
    pub b: u32,
}

#[repr(Rust)]
pub struct SingleFieldRust {
    pub a: u32,
}

#[repr(Rust)]
pub struct EmptyRust;

#[repr(Rust)]
pub struct AllZstRust {
    pub a: (),
    pub b: [u8; 0],
    pub c: PhantomData<u64>,
}

#[repr(Rust)]
pub struct AllZstAlignedRust {
    pub a: (),
    pub b: [u32; 0],
    pub c: [u64; 0],
}

#[repr(C)]
pub struct EmptyC;

#[repr(C)]
pub struct AllZstAlignedC {
    pub a: (),
    pub b: [u32; 0],
}

#[repr(transparent)]
pub struct TransAllZst {
    pub a: (),
    pub b: [u8; 0],
}

#[repr(transparent)]
pub struct TransWithZst {
    pub z0: (),
    pub val: u64,
    pub z1: [u8; 0],
    pub z2: PhantomData<u32>,
}

#[repr(C)]
pub struct OuterCWithInnerRust {
    pub prefix: u8,
    pub inner: Sandwich,
}

#[repr(Rust)]
pub struct MaybeUnsizedTail<T: ?Sized> {
    pub a: [u8; 3],
    pub b: u16,
    pub tail: T,
}

#[repr(Rust)]
pub struct NicheBiasStruct {
    pub a: u32,
    pub b: (bool, u8),
    pub c: u16,
}

// Compile-time assertions verifying the exact layout properties
const _: () = {
    assert!(size_of::<Sandwich>() == 4);
    assert!(align_of::<Sandwich>() == 2);
    assert!(size_of::<CSandwich>() == 6);
    assert!(align_of::<CSandwich>() == 2);

    assert!(size_of::<InevitablePad>() == 8);
    assert!(align_of::<InevitablePad>() == 4);

    assert!(size_of::<TwoU24>() == 12);
    assert!(align_of::<TwoU24>() == 4);

    assert!(size_of::<Mixed>() == 16);
    assert!(align_of::<Mixed>() == 8);

    assert!(size_of::<EmptyRust>() == 0);
    assert!(align_of::<EmptyRust>() == 1);
    assert!(size_of::<AllZstRust>() == 0);
    assert!(align_of::<AllZstRust>() == 1);
    assert!(size_of::<AllZstAlignedRust>() == 0);
    assert!(align_of::<AllZstAlignedRust>() == 8);

    assert!(size_of::<TransAllZst>() == 0);
    assert!(align_of::<TransAllZst>() == 1);
    assert!(size_of::<TransWithZst>() == 8);
    assert!(align_of::<TransWithZst>() == 8);
    assert!(offset_of!(TransWithZst, val) == 0);
};

fn main() {
    println!(
        "Sandwich: size={}, align={}, offsets=({}, {}, {})",
        size_of::<Sandwich>(),
        align_of::<Sandwich>(),
        offset_of!(Sandwich, a),
        offset_of!(Sandwich, b),
        offset_of!(Sandwich, c),
    );
    println!(
        "CSandwich: size={}, align={}, offsets=({}, {}, {})",
        size_of::<CSandwich>(),
        align_of::<CSandwich>(),
        offset_of!(CSandwich, a),
        offset_of!(CSandwich, b),
        offset_of!(CSandwich, c),
    );
    println!(
        "InevitablePad: size={}, align={}, offsets=({}, {})",
        size_of::<InevitablePad>(),
        align_of::<InevitablePad>(),
        offset_of!(InevitablePad, a),
        offset_of!(InevitablePad, b),
    );
    println!(
        "TwoU24: size={}, align={}, offsets=({}, {}, {})",
        size_of::<TwoU24>(),
        align_of::<TwoU24>(),
        offset_of!(TwoU24, a),
        offset_of!(TwoU24, b),
        offset_of!(TwoU24, c),
    );
    println!(
        "Mixed: size={}, align={}, offsets=({}, {})",
        size_of::<Mixed>(),
        align_of::<Mixed>(),
        offset_of!(Mixed, a),
        offset_of!(Mixed, b),
    );
    println!(
        "OuterCWithInnerRust: size={}, align={}, offsets=({}, {})",
        size_of::<OuterCWithInnerRust>(),
        align_of::<OuterCWithInnerRust>(),
        offset_of!(OuterCWithInnerRust, prefix),
        offset_of!(OuterCWithInnerRust, inner),
    );
    println!(
        "MaybeUnsizedTail<u16>: size={}, align={}, offsets=({}, {}, {})",
        size_of::<MaybeUnsizedTail<u16>>(),
        align_of::<MaybeUnsizedTail<u16>>(),
        offset_of!(MaybeUnsizedTail<u16>, a),
        offset_of!(MaybeUnsizedTail<u16>, b),
        offset_of!(MaybeUnsizedTail<u16>, tail),
    );
    println!(
        "Tuple ([u8; 3], u16, u16): size={}, align={}, offsets=({}, {}, {})",
        size_of::<([u8; 3], u16, u16)>(),
        align_of::<([u8; 3], u16, u16)>(),
        offset_of!(([u8; 3], u16, u16), 0),
        offset_of!(([u8; 3], u16, u16), 1),
        offset_of!(([u8; 3], u16, u16), 2),
    );
    println!(
        "NicheBiasStruct: size={}, align={}, offsets=({}, {}, {})",
        size_of::<NicheBiasStruct>(),
        align_of::<NicheBiasStruct>(),
        offset_of!(NicheBiasStruct, a),
        offset_of!(NicheBiasStruct, b),
        offset_of!(NicheBiasStruct, c),
    );
    println!(
        "AllZstRust: size={}, align={}; AllZstAlignedRust: size={}, align={}",
        size_of::<AllZstRust>(),
        align_of::<AllZstRust>(),
        size_of::<AllZstAlignedRust>(),
        align_of::<AllZstAlignedRust>(),
    );
    println!(
        "TransWithZst: size={}, align={}, offsets=({}, {}, {}, {})",
        size_of::<TransWithZst>(),
        align_of::<TransWithZst>(),
        offset_of!(TransWithZst, z0),
        offset_of!(TransWithZst, val),
        offset_of!(TransWithZst, z1),
        offset_of!(TransWithZst, z2),
    );
}
