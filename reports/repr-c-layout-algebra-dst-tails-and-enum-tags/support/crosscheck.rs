use std::ffi::c_int;
use std::mem::{align_of, align_of_val, offset_of, size_of, size_of_val};

// 1. Empty repr(C) struct
#[repr(C)]
struct Empty;

// 2. Ascending alignments with internal and trailing padding
#[repr(C)]
struct AscPad {
    a: u8,
    b: u32,
    c: u16,
}

// 3. Rust Reference ThreeInts example
#[repr(C)]
struct ThreeInts {
    first: i16,
    second: i8,
    third: i32,
}

// 4. Trailing padding only
#[repr(C)]
struct TrailPad {
    a: u16,
    b: u8,
}

// 5. Inter-field padding (1-byte, 2-byte)
#[repr(C)]
struct U8U16 {
    a: u8,
    b: u16,
}

// 6. Aligned zero-sized field in the middle
#[repr(C)]
struct ZstMid {
    a: u8,
    z: [u32; 0],
    b: u8,
}

// 7. Homogeneous struct
#[repr(C)]
struct Homog {
    a: u32,
    b: u32,
    c: u32,
}

// 8. packed(1)
#[repr(C, packed(1))]
struct Packed1 {
    a: u8,
    b: u32,
    c: u16,
}

// 9. packed(2)
#[repr(C, packed(2))]
struct Packed2 {
    a: u8,
    b: u32,
    c: u8,
}

// 10. packed(8) no-op (N >= max field align 4)
#[repr(C, packed(8))]
struct PackedNoop {
    a: u8,
    b: u32,
    c: u16,
}

// 11. align(8) raising alignment from 2 to 8
#[repr(C, align(8))]
struct Aligned8 {
    a: u16,
    b: u8,
}

// 12. align(2) no-op (N <= natural align 4)
#[repr(C, align(2))]
struct AlignedNoop {
    a: u8,
    b: u32,
    c: u16,
}

// 13. repr(C) union whose size rounds up to alignment
#[repr(C)]
union SizeRoundedUp {
    a: u32,
    b: [u16; 3],
}

// 14. Field-less repr(C) enum (small discriminants)
#[repr(C)]
#[allow(dead_code)]
enum FieldlessC {
    A,
    B,
}

// 14b. Field-less repr(C) enum with large discriminant exceeding c_int / c_uint.
// Note: Discriminants outside the target C `int` / `unsigned int` range are non-conforming per
// the Rust Reference (`r[layout.repr.c.enum.discriminant]`). `rustc` currently accepts them and
// widens the tag to 8 bytes, but emits the future-incompatibility lint
// `repr_c_enums_larger_than_int` (tracking issue rust-lang/rust#124403), silenced here solely
// to observe `rustc`'s current layout behavior.
#[repr(C)]
#[allow(dead_code, repr_c_enums_larger_than_int)]
enum FieldlessCBigDiscr {
    A = 0x1_0000_0000,
    B,
}

// 15. Rust Reference EnumC (small discriminants)
#[repr(C)]
#[allow(dead_code)]
enum EnumC {
    Variant0(u8),
    Variant1,
}

// 16. Rust Reference multi-variant repr(C) enum
#[repr(C)]
#[allow(dead_code)]
enum RefEnum {
    A(u32),
    B(f32, u64),
    C { x: u32, y: u8 },
    D,
}

// 17. repr(C, u8) vs repr(u8) divergence
#[repr(C, u8)]
#[allow(dead_code)]
enum EnumCU8 {
    A(u8, u16),
    B,
}

#[repr(u8)]
#[allow(dead_code)]
enum EnumU8 {
    A(u8, u16),
    B,
}

// 18. Slice-tailed DSTs (unsized via generic tail T: ?Sized)
#[repr(C)]
struct DstTrailPad<T: ?Sized> {
    hdr: u32,
    tail: T,
}

#[repr(C)]
struct DstUnalignedOff<T: ?Sized> {
    hdr: u16,
    tag: u8,
    tail: T,
}

#[repr(C, packed(1))]
struct DstPacked1 {
    hdr: u32,
    tail: [u8],
}

#[repr(C, packed(2))]
struct DstPacked2 {
    hdr: u8,
    tail: [u32],
}

#[repr(C, align(4))]
struct DstAlign4Elem3<T: ?Sized> {
    a: u8,
    tail: T,
}

fn check_dst_trail_pad<const N: usize>() -> (usize, usize) {
    let v = DstTrailPad { hdr: 0, tail: [0u8; N] };
    let r: &DstTrailPad<[u8]> = &v;
    (size_of_val(r), align_of_val(r))
}

fn check_dst_unaligned_off<const N: usize>() -> (usize, usize) {
    let v = DstUnalignedOff { hdr: 0, tag: 0, tail: [0u8; N] };
    let r: &DstUnalignedOff<[u8]> = &v;
    (size_of_val(r), align_of_val(r))
}

fn check_dst_unaligned_off_elem2<const N: usize>() -> (usize, usize) {
    let v = DstUnalignedOff { hdr: 0, tag: 0, tail: [[0u8; 2]; N] };
    let r: &DstUnalignedOff<[[u8; 2]]> = &v;
    (size_of_val(r), align_of_val(r))
}

fn check_dst_packed1(n: usize) -> (usize, usize, usize) {
    let buf = [0u8; 64];
    let slice_ptr: *const [u8] = &buf[..n];
    let dst_ptr: *const DstPacked1 = slice_ptr as *const DstPacked1;
    // SAFETY: `buf` is 64 initialized bytes, `DstPacked1` has alignment 1 and size `4 + n <= 64`.
    let r: &DstPacked1 = unsafe { &*dst_ptr };
    let tail_off = (unsafe { &raw const (*dst_ptr).tail } as *const u8 as usize)
        - (dst_ptr as *const u8 as usize);
    (size_of_val(r), align_of_val(r), tail_off)
}

fn check_dst_packed2(n: usize) -> (usize, usize, usize) {
    let buf = [0u16; 64];
    let slice_ptr: *const [u16] = &buf[..n];
    let dst_ptr: *const DstPacked2 = slice_ptr as *const DstPacked2;
    // SAFETY: `buf` is 128 initialized bytes aligned to 2, `DstPacked2` has alignment 2 and size `2 + 4*n <= 128`.
    let r: &DstPacked2 = unsafe { &*dst_ptr };
    let tail_off = (unsafe { &raw const (*dst_ptr).tail } as *const u8 as usize)
        - (dst_ptr as *const u8 as usize);
    (size_of_val(r), align_of_val(r), tail_off)
}

fn check_dst_align4_elem3<const N: usize>() -> (usize, usize) {
    let v = DstAlign4Elem3 { a: 0, tail: [[0u8; 3]; N] };
    let r: &DstAlign4Elem3<[[u8; 3]]> = &v;
    (size_of_val(r), align_of_val(r))
}

fn main() {
    println!("c_int: size={} align={}", size_of::<c_int>(), align_of::<c_int>());
    println!("usize: size={} align={}", size_of::<usize>(), align_of::<usize>());

    println!("01 Empty: size={} align={} offsets=[]",
        size_of::<Empty>(), align_of::<Empty>());
    println!("02 AscPad: size={} align={} offsets=[{}, {}, {}]",
        size_of::<AscPad>(), align_of::<AscPad>(),
        offset_of!(AscPad, a), offset_of!(AscPad, b), offset_of!(AscPad, c));
    println!("03 ThreeInts: size={} align={} offsets=[{}, {}, {}]",
        size_of::<ThreeInts>(), align_of::<ThreeInts>(),
        offset_of!(ThreeInts, first), offset_of!(ThreeInts, second), offset_of!(ThreeInts, third));
    println!("04 TrailPad: size={} align={} offsets=[{}, {}]",
        size_of::<TrailPad>(), align_of::<TrailPad>(),
        offset_of!(TrailPad, a), offset_of!(TrailPad, b));
    println!("05 U8U16: size={} align={} offsets=[{}, {}]",
        size_of::<U8U16>(), align_of::<U8U16>(),
        offset_of!(U8U16, a), offset_of!(U8U16, b));
    println!("06 ZstMid: size={} align={} offsets=[{}, {}, {}]",
        size_of::<ZstMid>(), align_of::<ZstMid>(),
        offset_of!(ZstMid, a), offset_of!(ZstMid, z), offset_of!(ZstMid, b));
    println!("07 Homog: size={} align={} offsets=[{}, {}, {}]",
        size_of::<Homog>(), align_of::<Homog>(),
        offset_of!(Homog, a), offset_of!(Homog, b), offset_of!(Homog, c));
    println!("08 Packed1: size={} align={} offsets=[{}, {}, {}]",
        size_of::<Packed1>(), align_of::<Packed1>(),
        offset_of!(Packed1, a), offset_of!(Packed1, b), offset_of!(Packed1, c));
    println!("09 Packed2: size={} align={} offsets=[{}, {}, {}]",
        size_of::<Packed2>(), align_of::<Packed2>(),
        offset_of!(Packed2, a), offset_of!(Packed2, b), offset_of!(Packed2, c));
    println!("10 PackedNoop: size={} align={} offsets=[{}, {}, {}]",
        size_of::<PackedNoop>(), align_of::<PackedNoop>(),
        offset_of!(PackedNoop, a), offset_of!(PackedNoop, b), offset_of!(PackedNoop, c));
    println!("11 Aligned8: size={} align={} offsets=[{}, {}]",
        size_of::<Aligned8>(), align_of::<Aligned8>(),
        offset_of!(Aligned8, a), offset_of!(Aligned8, b));
    println!("12 AlignedNoop: size={} align={} offsets=[{}, {}, {}]",
        size_of::<AlignedNoop>(), align_of::<AlignedNoop>(),
        offset_of!(AlignedNoop, a), offset_of!(AlignedNoop, b), offset_of!(AlignedNoop, c));
    println!("13 SizeRoundedUp: size={} align={} offsets=[{}, {}]",
        size_of::<SizeRoundedUp>(), align_of::<SizeRoundedUp>(),
        offset_of!(SizeRoundedUp, a), offset_of!(SizeRoundedUp, b));
    println!("14 FieldlessC: size={} align={}",
        size_of::<FieldlessC>(), align_of::<FieldlessC>());
    println!("14b FieldlessCBigDiscr: size={} align={}",
        size_of::<FieldlessCBigDiscr>(), align_of::<FieldlessCBigDiscr>());

    let ec = EnumC::Variant0(0);
    let ec_v0 = match &ec {
        EnumC::Variant0(x) => (x as *const u8 as usize) - (&ec as *const EnumC as usize),
        _ => unreachable!(),
    };
    println!("15 EnumC: size={} align={} variant0_offsets=[{}]",
        size_of::<EnumC>(), align_of::<EnumC>(), ec_v0);

    let re_a = RefEnum::A(0);
    let re_a_off = match &re_a {
        RefEnum::A(x) => (x as *const u32 as usize) - (&re_a as *const RefEnum as usize),
        _ => unreachable!(),
    };
    let re_b = RefEnum::B(0.0, 0);
    let (re_b0, re_b1) = match &re_b {
        RefEnum::B(x, y) => (
            (x as *const f32 as usize) - (&re_b as *const RefEnum as usize),
            (y as *const u64 as usize) - (&re_b as *const RefEnum as usize),
        ),
        _ => unreachable!(),
    };
    let re_c = RefEnum::C { x: 0, y: 0 };
    let (re_c0, re_c1) = match &re_c {
        RefEnum::C { x, y } => (
            (x as *const u32 as usize) - (&re_c as *const RefEnum as usize),
            (y as *const u8 as usize) - (&re_c as *const RefEnum as usize),
        ),
        _ => unreachable!(),
    };
    println!("16 RefEnum: size={} align={} variant_offsets=[[{}], [{}, {}], [{}, {}], []]",
        size_of::<RefEnum>(), align_of::<RefEnum>(), re_a_off, re_b0, re_b1, re_c0, re_c1);

    let ecu8 = EnumCU8::A(0, 0);
    let (ecu8_0, ecu8_1) = match &ecu8 {
        EnumCU8::A(x, y) => (
            (x as *const u8 as usize) - (&ecu8 as *const EnumCU8 as usize),
            (y as *const u16 as usize) - (&ecu8 as *const EnumCU8 as usize),
        ),
        _ => unreachable!(),
    };
    println!("17a EnumCU8: size={} align={} variantA_offsets=[{}, {}]",
        size_of::<EnumCU8>(), align_of::<EnumCU8>(), ecu8_0, ecu8_1);

    let eu8 = EnumU8::A(0, 0);
    let (eu8_0, eu8_1) = match &eu8 {
        EnumU8::A(x, y) => (
            (x as *const u8 as usize) - (&eu8 as *const EnumU8 as usize),
            (y as *const u16 as usize) - (&eu8 as *const EnumU8 as usize),
        ),
        _ => unreachable!(),
    };
    println!("17b EnumU8: size={} align={} variantA_offsets=[{}, {}]",
        size_of::<EnumU8>(), align_of::<EnumU8>(), eu8_0, eu8_1);

    println!("18a DstTrailPad: tail_offset={} align={} sizes_0_to_5=[{}, {}, {}, {}, {}, {}]",
        offset_of!(DstTrailPad<[u8; 0]>, tail),
        check_dst_trail_pad::<0>().1,
        check_dst_trail_pad::<0>().0,
        check_dst_trail_pad::<1>().0,
        check_dst_trail_pad::<2>().0,
        check_dst_trail_pad::<3>().0,
        check_dst_trail_pad::<4>().0,
        check_dst_trail_pad::<5>().0);

    println!("18b DstUnalignedOff: tail_offset={} align={} sizes_0_to_5=[{}, {}, {}, {}, {}, {}]",
        offset_of!(DstUnalignedOff<[u8; 0]>, tail),
        check_dst_unaligned_off::<0>().1,
        check_dst_unaligned_off::<0>().0,
        check_dst_unaligned_off::<1>().0,
        check_dst_unaligned_off::<2>().0,
        check_dst_unaligned_off::<3>().0,
        check_dst_unaligned_off::<4>().0,
        check_dst_unaligned_off::<5>().0);

    println!("18c DstPacked1: tail_offset={} align={} sizes_0_to_3=[{}, {}, {}, {}]",
        check_dst_packed1(0).2,
        check_dst_packed1(0).1,
        check_dst_packed1(0).0,
        check_dst_packed1(1).0,
        check_dst_packed1(2).0,
        check_dst_packed1(3).0);

    println!("18d DstPacked2: tail_offset={} align={} sizes_0_to_3=[{}, {}, {}, {}]",
        check_dst_packed2(0).2,
        check_dst_packed2(0).1,
        check_dst_packed2(0).0,
        check_dst_packed2(1).0,
        check_dst_packed2(2).0,
        check_dst_packed2(3).0);

    println!("18e DstAlign4Elem3: tail_offset={} align={} sizes_0_to_4=[{}, {}, {}, {}, {}]",
        offset_of!(DstAlign4Elem3<[[u8; 3]; 0]>, tail),
        check_dst_align4_elem3::<0>().1,
        check_dst_align4_elem3::<0>().0,
        check_dst_align4_elem3::<1>().0,
        check_dst_align4_elem3::<2>().0,
        check_dst_align4_elem3::<3>().0,
        check_dst_align4_elem3::<4>().0);

    println!("18f DstUnalignedOffElem2: tail_offset={} align={} sizes_0_to_3=[{}, {}, {}, {}]",
        offset_of!(DstUnalignedOff<[[u8; 2]; 0]>, tail),
        check_dst_unaligned_off_elem2::<0>().1,
        check_dst_unaligned_off_elem2::<0>().0,
        check_dst_unaligned_off_elem2::<1>().0,
        check_dst_unaligned_off_elem2::<2>().0,
        check_dst_unaligned_off_elem2::<3>().0);
}
