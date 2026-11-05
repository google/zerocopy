// Reproducible layout and ABI verification probes across Rust type constructors.
// Executed under both stable (1.99.1) and nightly-2026-05-31 (1.98.0-nightly,
// default and `-Z randomize-layout -Z layout-seed=42` / `7`).

#![allow(dead_code)]
#![cfg_attr(feature = "nightly_never", feature(never_type))]

use std::cell::{Cell, UnsafeCell};
use std::cmp::Ordering;
use std::convert::Infallible;
use std::marker::PhantomData;
use std::mem::{align_of, align_of_val, offset_of, size_of, size_of_val, transmute, ManuallyDrop, MaybeUninit};
use std::num::{NonZeroI32, NonZeroU128, NonZeroU32, NonZeroU8, NonZeroUsize};
use std::ptr::{addr_of, NonNull};

// ---------------------------------------------------------------------------
// Tuples and Default #[repr(Rust)] Structs / ZSTs
// ---------------------------------------------------------------------------

struct EmptyRust;
struct ZstUnitFields((), PhantomData<u64>);

#[repr(align(4))]
struct ZstAlign4;

struct ZstWithAlign4Field(ZstAlign4, ());

enum SingleVariantZstEnum {
    Only((), PhantomData<u64>),
}

enum EmptyEnum {}

struct SingleU64(u64);
struct PairU32(u32, u32);
struct TripleHet(u8, u32, u16);

// ---------------------------------------------------------------------------
// #[repr(C)], #[repr(transparent)], #[repr(packed(N))], #[repr(align(N))]
// ---------------------------------------------------------------------------

#[repr(C)]
struct EmptyC;

#[repr(C)]
struct CWithZstAlign1 {
    a: u8,
    z: (),
    b: u8,
}

#[repr(C)]
struct CWithZstAlign4 {
    a: u8,
    z: [u32; 0],
    b: u8,
}

#[repr(C)]
struct CTrailingZstAlign4 {
    a: u8,
    z: [u32; 0],
}

#[repr(transparent)]
struct TransparentWith1Zst<T: ?Sized> {
    z1: (),
    z2: PhantomData<u64>,
    inner: T,
}

#[repr(transparent)]
struct TransparentOverAlign4Zst {
    z1: (),
    z_align4: [u32; 0],
}

#[repr(packed(1))]
struct RustPacked1Het {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(C, packed(1))]
struct CPacked1Het {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(C, packed(2))]
struct CPacked2Het {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(align(16))]
struct RustAlign16Het {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(C, align(16))]
struct CAlign16Het {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(C, align(16))]
struct InnerCAlign16 {
    a: u8,
    b: u8,
}

#[repr(C, packed(2))]
struct GenericOuterCPacked2<T> {
    x: u8,
    inner: T,
}

// ---------------------------------------------------------------------------
// Unions (#[repr(Rust)] union vs #[repr(C)] union)
// ---------------------------------------------------------------------------

union RustUnion {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(C)]
union CUnion {
    a: u8,
    b: u32,
    c: u16,
}

#[repr(packed(1))]
union RustPackedUnion {
    a: u8,
    b: u32,
}

#[repr(C, align(16))]
union CAlign16Union {
    a: u8,
    b: u32,
}

// ---------------------------------------------------------------------------
// Enums & Niche Optimizations
// ---------------------------------------------------------------------------

#[repr(C)]
enum CEnumFieldless {
    A,
    B,
}

#[repr(u8)]
enum U8EnumFieldless {
    A,
    B,
}

#[repr(C)]
enum CEnumWithFields {
    A(u8),
    B(u64),
}

#[repr(u8)]
enum U8EnumWithFields {
    A(u8),
    B(u64),
}

#[repr(C, u8)]
enum CU8EnumWithFields {
    A(u8),
    B(u64),
}

enum RustEnumWithFields {
    A(u8),
    B(u64),
}

#[repr(u8)]
enum UserBoundedEnum {
    V1 = 1,
    V2 = 2,
}

// ---------------------------------------------------------------------------
// Unsized / Dynamically Sized Structs (DSTs)
// ---------------------------------------------------------------------------

#[repr(C)]
struct CDst<T: ?Sized> {
    header: u8,
    tail: T,
}

struct RustDst<T: ?Sized> {
    a: u8,
    b: u32,
    tail: T,
}

// Note: packed structs with unsized tails require that the tail statically does
// not need Drop (`T: Copy`), because dropping an unaligned field moves it onto
// the stack first, which is impossible for an unsized tail.
#[repr(C, packed(2))]
struct CPacked2Dst<T: Copy> {
    header: u8,
    tail: [T],
}

#[repr(C)]
struct InnerUnalignedTail<T: Copy> {
    b: u8,
    tail: [T],
}

#[repr(C, packed(2))]
struct OuterPacked2OverInnerDst<T: Copy> {
    a: u8,
    inner: InnerUnalignedTail<T>,
}

trait SampleTrait {
    fn val(&self) -> usize;
}
impl SampleTrait for u8 {
    fn val(&self) -> usize { *self as usize }
}
impl SampleTrait for u64 {
    fn val(&self) -> usize { *self as usize }
}
#[repr(align(32))]
struct Align32Struct([u8; 32]);
impl SampleTrait for Align32Struct {
    fn val(&self) -> usize { 32 }
}

fn main() {
    println!("{{");
    println!("  \"compiler_mode\": {:?},", std::env::args().nth(1).unwrap_or_else(|| "default".to_string()));

    // 1. Primitives & Pointers
    println!("  \"primitives_and_pointers\": {{");
    println!("    \"bool\": {{\"size\": {}, \"align\": {}}},", size_of::<bool>(), align_of::<bool>());
    println!("    \"u8\": {{\"size\": {}, \"align\": {}}},", size_of::<u8>(), align_of::<u8>());
    println!("    \"i8\": {{\"size\": {}, \"align\": {}}},", size_of::<i8>(), align_of::<i8>());
    println!("    \"u16\": {{\"size\": {}, \"align\": {}}},", size_of::<u16>(), align_of::<u16>());
    println!("    \"i16\": {{\"size\": {}, \"align\": {}}},", size_of::<i16>(), align_of::<i16>());
    println!("    \"u32\": {{\"size\": {}, \"align\": {}}},", size_of::<u32>(), align_of::<u32>());
    println!("    \"i32\": {{\"size\": {}, \"align\": {}}},", size_of::<i32>(), align_of::<i32>());
    println!("    \"u64\": {{\"size\": {}, \"align\": {}}},", size_of::<u64>(), align_of::<u64>());
    println!("    \"i64\": {{\"size\": {}, \"align\": {}}},", size_of::<i64>(), align_of::<i64>());
    println!("    \"u128\": {{\"size\": {}, \"align\": {}}},", size_of::<u128>(), align_of::<u128>());
    println!("    \"i128\": {{\"size\": {}, \"align\": {}}},", size_of::<i128>(), align_of::<i128>());
    println!("    \"usize\": {{\"size\": {}, \"align\": {}}},", size_of::<usize>(), align_of::<usize>());
    println!("    \"isize\": {{\"size\": {}, \"align\": {}}},", size_of::<isize>(), align_of::<isize>());
    println!("    \"f32\": {{\"size\": {}, \"align\": {}}},", size_of::<f32>(), align_of::<f32>());
    println!("    \"f64\": {{\"size\": {}, \"align\": {}}},", size_of::<f64>(), align_of::<f64>());
    println!("    \"char\": {{\"size\": {}, \"align\": {}}},", size_of::<char>(), align_of::<char>());
    println!("    \"unit\": {{\"size\": {}, \"align\": {}}},", size_of::<()>(), align_of::<()>());
    #[cfg(feature = "nightly_never")]
    println!("    \"never\": {{\"size\": {}, \"align\": {}}},", size_of::<!>(), align_of::<!>());
    println!("    \"empty_enum_never_equiv\": {{\"size\": {}, \"align\": {}}},", size_of::<Infallible>(), align_of::<Infallible>());
    println!("    \"thin_ptr_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<*const u8>(), align_of::<*const u8>());
    println!("    \"fn_ptr\": {{\"size\": {}, \"align\": {}}},", size_of::<fn()>(), align_of::<fn()>());
    println!("    \"wide_ptr_slice\": {{\"size\": {}, \"align\": {}}},", size_of::<*const [u8]>(), align_of::<*const [u8]>());
    println!("    \"wide_ptr_str\": {{\"size\": {}, \"align\": {}}},", size_of::<*const str>(), align_of::<*const str>());
    println!("    \"wide_ptr_dyn\": {{\"size\": {}, \"align\": {}}}", size_of::<*const dyn SampleTrait>(), align_of::<*const dyn SampleTrait>());
    println!("  }},");

    // Wide pointer internal field order probe: (data_ptr, metadata)
    let arr: [u16; 5] = [10, 20, 30, 40, 50];
    let slice_ref: &[u16] = &arr[..];
    let raw_words: [usize; 2] = unsafe { transmute(slice_ref) };
    let data_addr = arr.as_ptr() as usize;
    println!("  \"wide_pointer_words\": {{");
    println!("    \"word0_is_data_ptr\": {},", raw_words[0] == data_addr);
    println!("    \"word1_len_metadata\": {}", raw_words[1]);
    println!("  }},");

    // 2. Arrays and Slices
    let sample_slice: &[u32] = &[1, 2, 3];
    println!("  \"arrays_and_slices\": {{");
    println!("    \"array_u32_0\": {{\"size\": {}, \"align\": {}}},", size_of::<[u32; 0]>(), align_of::<[u32; 0]>());
    println!("    \"array_u32_3\": {{\"size\": {}, \"align\": {}}},", size_of::<[u32; 3]>(), align_of::<[u32; 3]>());
    println!("    \"slice_u32_3_val\": {{\"size\": {}, \"align\": {}}}", size_of_val(sample_slice), align_of_val(sample_slice));
    println!("  }},");

    // 3. Tuples and Default #[repr(Rust)] Structs / ZSTs
    println!("  \"tuples_and_repr_rust\": {{");
    println!("    \"unit_tuple\": {{\"size\": {}, \"align\": {}}},", size_of::<()>(), align_of::<()>());
    println!("    \"nested_unit_tuple\": {{\"size\": {}, \"align\": {}}},", size_of::<((), ())>(), align_of::<((), ())>());
    println!("    \"tuple_with_align4_zst\": {{\"size\": {}, \"align\": {}}},", size_of::<((), [u32; 0])>(), align_of::<((), [u32; 0])>());
    println!("    \"empty_rust_struct\": {{\"size\": {}, \"align\": {}}},", size_of::<EmptyRust>(), align_of::<EmptyRust>());
    println!("    \"zst_unit_fields_struct\": {{\"size\": {}, \"align\": {}}},", size_of::<ZstUnitFields>(), align_of::<ZstUnitFields>());
    println!("    \"zst_with_align4_field\": {{\"size\": {}, \"align\": {}}},", size_of::<ZstWithAlign4Field>(), align_of::<ZstWithAlign4Field>());
    println!("    \"single_variant_zst_enum\": {{\"size\": {}, \"align\": {}}},", size_of::<SingleVariantZstEnum>(), align_of::<SingleVariantZstEnum>());
    println!("    \"single_u64\": {{\"size\": {}, \"align\": {}, \"off0\": {}}},", size_of::<SingleU64>(), align_of::<SingleU64>(), offset_of!(SingleU64, 0));
    println!("    \"pair_u32\": {{\"size\": {}, \"align\": {}, \"off0\": {}, \"off1\": {}}},",
        size_of::<PairU32>(), align_of::<PairU32>(), offset_of!(PairU32, 0), offset_of!(PairU32, 1));
    println!("    \"triple_het\": {{\"size\": {}, \"align\": {}, \"off0_u8\": {}, \"off1_u32\": {}, \"off2_u16\": {}}},",
        size_of::<TripleHet>(), align_of::<TripleHet>(), offset_of!(TripleHet, 0), offset_of!(TripleHet, 1), offset_of!(TripleHet, 2));
    println!("    \"tuple_het\": {{\"size\": {}, \"align\": {}, \"off0_u8\": {}, \"off1_u32\": {}, \"off2_u16\": {}}}",
        size_of::<(u8, u32, u16)>(), align_of::<(u8, u32, u16)>(),
        offset_of!((u8, u32, u16), 0), offset_of!((u8, u32, u16), 1), offset_of!((u8, u32, u16), 2));
    println!("  }},");

    // 4. #[repr(C)], #[repr(transparent)], #[repr(packed(N))], #[repr(align(N))]
    println!("  \"repr_c_transparent_packed_align\": {{");
    println!("    \"empty_c\": {{\"size\": {}, \"align\": {}}},", size_of::<EmptyC>(), align_of::<EmptyC>());
    println!("    \"c_with_zst_align1\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_z\": {}, \"off_b\": {}}},",
        size_of::<CWithZstAlign1>(), align_of::<CWithZstAlign1>(),
        offset_of!(CWithZstAlign1, a), offset_of!(CWithZstAlign1, z), offset_of!(CWithZstAlign1, b));
    println!("    \"c_with_zst_align4\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_z\": {}, \"off_b\": {}}},",
        size_of::<CWithZstAlign4>(), align_of::<CWithZstAlign4>(),
        offset_of!(CWithZstAlign4, a), offset_of!(CWithZstAlign4, z), offset_of!(CWithZstAlign4, b));
    println!("    \"c_trailing_zst_align4\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_z\": {}}},",
        size_of::<CTrailingZstAlign4>(), align_of::<CTrailingZstAlign4>(),
        offset_of!(CTrailingZstAlign4, a), offset_of!(CTrailingZstAlign4, z));
    println!("    \"transparent_over_u32\": {{\"size\": {}, \"align\": {}, \"off_inner\": {}}},",
        size_of::<TransparentWith1Zst<u32>>(), align_of::<TransparentWith1Zst<u32>>(),
        offset_of!(TransparentWith1Zst<u32>, inner));
    println!("    \"transparent_over_align4_zst\": {{\"size\": {}, \"align\": {}}},",
        size_of::<TransparentOverAlign4Zst>(), align_of::<TransparentOverAlign4Zst>());
    println!("    \"rust_packed1_het\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_c\": {}}},",
        size_of::<RustPacked1Het>(), align_of::<RustPacked1Het>(),
        offset_of!(RustPacked1Het, a), offset_of!(RustPacked1Het, b), offset_of!(RustPacked1Het, c));
    println!("    \"c_packed1_het\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_c\": {}}},",
        size_of::<CPacked1Het>(), align_of::<CPacked1Het>(),
        offset_of!(CPacked1Het, a), offset_of!(CPacked1Het, b), offset_of!(CPacked1Het, c));
    println!("    \"c_packed2_het\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_c\": {}}},",
        size_of::<CPacked2Het>(), align_of::<CPacked2Het>(),
        offset_of!(CPacked2Het, a), offset_of!(CPacked2Het, b), offset_of!(CPacked2Het, c));
    println!("    \"rust_align16_het\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_c\": {}}},",
        size_of::<RustAlign16Het>(), align_of::<RustAlign16Het>(),
        offset_of!(RustAlign16Het, a), offset_of!(RustAlign16Het, b), offset_of!(RustAlign16Het, c));
    println!("    \"c_align16_het\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_c\": {}}},",
        size_of::<CAlign16Het>(), align_of::<CAlign16Het>(),
        offset_of!(CAlign16Het, a), offset_of!(CAlign16Het, b), offset_of!(CAlign16Het, c));
    println!("    \"generic_outer_c_packed2_over_c_align16\": {{\"size\": {}, \"align\": {}, \"off_x\": {}, \"off_inner\": {}}}",
        size_of::<GenericOuterCPacked2<InnerCAlign16>>(), align_of::<GenericOuterCPacked2<InnerCAlign16>>(),
        offset_of!(GenericOuterCPacked2<InnerCAlign16>, x), offset_of!(GenericOuterCPacked2<InnerCAlign16>, inner));
    println!("  }},");

    // 5. Unions
    println!("  \"unions\": {{");
    println!("    \"rust_union\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_c\": {}}},",
        size_of::<RustUnion>(), align_of::<RustUnion>(),
        offset_of!(RustUnion, a), offset_of!(RustUnion, b), offset_of!(RustUnion, c));
    println!("    \"c_union\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_c\": {}}},",
        size_of::<CUnion>(), align_of::<CUnion>(),
        offset_of!(CUnion, a), offset_of!(CUnion, b), offset_of!(CUnion, c));
    println!("    \"rust_packed_union\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}}},",
        size_of::<RustPackedUnion>(), align_of::<RustPackedUnion>(),
        offset_of!(RustPackedUnion, a), offset_of!(RustPackedUnion, b));
    println!("    \"c_align16_union\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}}}",
        size_of::<CAlign16Union>(), align_of::<CAlign16Union>(),
        offset_of!(CAlign16Union, a), offset_of!(CAlign16Union, b));
    println!("  }},");

    // 6. Enums and Niche Optimizations
    let none_ref_is_zero = unsafe { transmute::<Option<&u8>, usize>(None) == 0 };
    let none_fn_is_zero = unsafe { transmute::<Option<fn()>, usize>(None) == 0 };
    let none_nz32_is_zero = unsafe { transmute::<Option<NonZeroU32>, u32>(None) == 0 };
    let err_unit_nz32_is_zero = unsafe { transmute::<Result<NonZeroU32, ()>, u32>(Err(())) == 0 };
    println!("  \"enums_and_niches\": {{");
    println!("    \"c_enum_fieldless\": {{\"size\": {}, \"align\": {}}},", size_of::<CEnumFieldless>(), align_of::<CEnumFieldless>());
    println!("    \"u8_enum_fieldless\": {{\"size\": {}, \"align\": {}}},", size_of::<U8EnumFieldless>(), align_of::<U8EnumFieldless>());
    println!("    \"c_enum_with_fields\": {{\"size\": {}, \"align\": {}}},", size_of::<CEnumWithFields>(), align_of::<CEnumWithFields>());
    println!("    \"u8_enum_with_fields\": {{\"size\": {}, \"align\": {}}},", size_of::<U8EnumWithFields>(), align_of::<U8EnumWithFields>());
    println!("    \"c_u8_enum_with_fields\": {{\"size\": {}, \"align\": {}}},", size_of::<CU8EnumWithFields>(), align_of::<CU8EnumWithFields>());
    println!("    \"rust_enum_with_fields\": {{\"size\": {}, \"align\": {}}},", size_of::<RustEnumWithFields>(), align_of::<RustEnumWithFields>());
    // Normatively guaranteed NPO types:
    println!("    \"opt_ref_u8\": {{\"size\": {}, \"align\": {}, \"none_is_zero\": {}}},", size_of::<Option<&u8>>(), align_of::<Option<&u8>>(), none_ref_is_zero);
    println!("    \"opt_mut_ref_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<&mut u8>>(), align_of::<Option<&mut u8>>());
    println!("    \"opt_ref_slice_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<&[u8]>>(), align_of::<Option<&[u8]>>());
    println!("    \"opt_box_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<Box<u8>>>(), align_of::<Option<Box<u8>>>());
    println!("    \"opt_box_slice_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<Box<[u8]>>>(), align_of::<Option<Box<[u8]>>>());
    println!("    \"opt_fn_ptr\": {{\"size\": {}, \"align\": {}, \"none_is_zero\": {}}},", size_of::<Option<fn()>>(), align_of::<Option<fn()>>(), none_fn_is_zero);
    println!("    \"opt_nonnull_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<NonNull<u8>>>(), align_of::<Option<NonNull<u8>>>());
    println!("    \"opt_nonnull_slice_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<NonNull<[u8]>>>(), align_of::<Option<NonNull<[u8]>>>());
    println!("    \"opt_nonzero_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<NonZeroU8>>(), align_of::<Option<NonZeroU8>>());
    println!("    \"opt_nonzero_u32\": {{\"size\": {}, \"align\": {}, \"none_is_zero\": {}}},", size_of::<Option<NonZeroU32>>(), align_of::<Option<NonZeroU32>>(), none_nz32_is_zero);
    println!("    \"opt_nonzero_i32\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<NonZeroI32>>(), align_of::<Option<NonZeroI32>>());
    println!("    \"opt_nonzero_u128\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<NonZeroU128>>(), align_of::<Option<NonZeroU128>>());
    println!("    \"opt_nonzero_usize\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<NonZeroUsize>>(), align_of::<Option<NonZeroUsize>>());
    println!("    \"opt_transparent_nonnull\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<TransparentWith1Zst<NonNull<u8>>>>(), align_of::<Option<TransparentWith1Zst<NonNull<u8>>>>());
    println!("    \"opt_manually_drop_ref\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<ManuallyDrop<&u8>>>(), align_of::<Option<ManuallyDrop<&u8>>>());
    // Guaranteed Result<T, E> with 1-ZST (library/core/src/result.rs:232-259):
    println!("    \"res_nonzero_u32_unit\": {{\"size\": {}, \"align\": {}, \"err_is_zero\": {}}},", size_of::<Result<NonZeroU32, ()>>(), align_of::<Result<NonZeroU32, ()>>(), err_unit_nz32_is_zero);
    println!("    \"res_unit_nonzero_u32\": {{\"size\": {}, \"align\": {}}},", size_of::<Result<(), NonZeroU32>>(), align_of::<Result<(), NonZeroU32>>());
    // Non-1-ZST in Result<T, E> (align 4 ZST): NOT guaranteed by result.rs, and actually changes alignment/size!
    println!("    \"res_nonzero_u8_zst_align4\": {{\"size\": {}, \"align\": {}}},", size_of::<Result<NonZeroU8, [u32; 0]>>(), align_of::<Result<NonZeroU8, [u32; 0]>>());
    // UnsafeCell / Cell / MaybeUninit traps:
    println!("    \"opt_unsafecell_ref_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<UnsafeCell<&u8>>>(), align_of::<Option<UnsafeCell<&u8>>>());
    println!("    \"opt_cell_ref_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<Cell<&u8>>>(), align_of::<Option<Cell<&u8>>>());
    println!("    \"opt_maybe_uninit_ref_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<MaybeUninit<&u8>>>(), align_of::<Option<MaybeUninit<&u8>>>());
    // Opportunistic (non-guaranteed) niches:
    println!("    \"opt_bool\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<bool>>(), align_of::<Option<bool>>());
    println!("    \"opt_char\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<char>>(), align_of::<Option<char>>());
    println!("    \"opt_ordering\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<Ordering>>(), align_of::<Option<Ordering>>());
    println!("    \"opt_infallible\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<Infallible>>(), align_of::<Option<Infallible>>());
    println!("    \"opt_opt_ref_u8\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<Option<&u8>>>(), align_of::<Option<Option<&u8>>>());
    println!("    \"opt_tuple_nz32_u32\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<(NonZeroU32, u32)>>(), align_of::<Option<(NonZeroU32, u32)>>());
    println!("    \"opt_array_nz32_2\": {{\"size\": {}, \"align\": {}}},", size_of::<Option<[NonZeroU32; 2]>>(), align_of::<Option<[NonZeroU32; 2]>>());
    println!("    \"opt_user_bounded_enum\": {{\"size\": {}, \"align\": {}}}", size_of::<Option<UserBoundedEnum>>(), align_of::<Option<UserBoundedEnum>>());
    println!("  }},");

    // 7. Unsized / Dynamically Sized Structs (DSTs)
    let c_dst_0: &CDst<[u32]> = &CDst { header: 1, tail: [0u32; 0] };
    let c_dst_1: &CDst<[u32]> = &CDst { header: 1, tail: [10u32; 1] };
    let c_dst_3: &CDst<[u32]> = &CDst { header: 1, tail: [10u32; 3] };
    let c_dst_off_tail = (addr_of!(c_dst_1.tail) as *const u32 as usize) - (c_dst_1 as *const CDst<[u32]> as *const u8 as usize);

    let rust_dst_2: &RustDst<[u16]> = &RustDst { a: 1, b: 2, tail: [3u16; 2] };
    let rust_dst_base = rust_dst_2 as *const RustDst<[u16]> as *const u8 as usize;
    let rust_dst_off_a = (addr_of!(rust_dst_2.a) as usize) - rust_dst_base;
    let rust_dst_off_b = (addr_of!(rust_dst_2.b) as usize) - rust_dst_base;
    let rust_dst_off_tail = (addr_of!(rust_dst_2.tail) as *const u16 as usize) - rust_dst_base;

    #[repr(C, packed(2))]
    struct CPacked2DstSized<const N: usize> {
        header: u8,
        tail: [u32; N],
    }
    let packed_dst_storage = CPacked2DstSized { header: 1, tail: [10u32; 1] };
    let packed_dst_1: &CPacked2Dst<u32> = unsafe {
        &*(std::ptr::slice_from_raw_parts(&packed_dst_storage as *const _ as *const u32, 1) as *const CPacked2Dst<u32>)
    };
    let packed_dst_off_tail = (addr_of!(packed_dst_1.tail) as *const u32 as usize) - (packed_dst_1 as *const CPacked2Dst<u32> as *const u8 as usize);

    #[repr(C)]
    struct InnerUnalignedTailSized<const N: usize> {
        b: u8,
        tail: [u32; N],
    }
    #[repr(C, packed(2))]
    struct OuterPacked2OverInnerDstSized<const N: usize> {
        a: u8,
        inner: InnerUnalignedTailSized<N>,
    }
    let nested_storage = OuterPacked2OverInnerDstSized {
        a: 1,
        inner: InnerUnalignedTailSized { b: 2, tail: [10u32; 1] },
    };
    let nested_packed_dst: &OuterPacked2OverInnerDst<u32> = unsafe {
        &*(std::ptr::slice_from_raw_parts(&nested_storage as *const _ as *const u32, 1) as *const OuterPacked2OverInnerDst<u32>)
    };
    let nested_base = nested_packed_dst as *const OuterPacked2OverInnerDst<u32> as *const u8 as usize;
    let nested_off_inner = (addr_of!(nested_packed_dst.inner) as *const u8 as usize) - nested_base;
    let nested_off_tail = (addr_of!(nested_packed_dst.inner.tail) as *const u32 as usize) - nested_base;

    let dyn_u8: &CDst<dyn SampleTrait> = &CDst { header: 1, tail: 7u8 };
    let dyn_u64: &CDst<dyn SampleTrait> = &CDst { header: 1, tail: 7u64 };
    let dyn_a32: &CDst<dyn SampleTrait> = &CDst { header: 1, tail: Align32Struct([0u8; 32]) };
    let dyn_u8_off = (addr_of!(dyn_u8.tail) as *const u8 as usize) - (dyn_u8 as *const CDst<dyn SampleTrait> as *const u8 as usize);
    let dyn_u64_off = (addr_of!(dyn_u64.tail) as *const u8 as usize) - (dyn_u64 as *const CDst<dyn SampleTrait> as *const u8 as usize);
    let dyn_a32_off = (addr_of!(dyn_a32.tail) as *const u8 as usize) - (dyn_a32 as *const CDst<dyn SampleTrait> as *const u8 as usize);

    println!("  \"unsized_dsts\": {{");
    println!("    \"c_dst_u32_len0\": {{\"size\": {}, \"align\": {}, \"tail_offset\": {}}},", size_of_val(c_dst_0), align_of_val(c_dst_0), c_dst_off_tail);
    println!("    \"c_dst_u32_len1\": {{\"size\": {}, \"align\": {}, \"tail_offset\": {}}},", size_of_val(c_dst_1), align_of_val(c_dst_1), c_dst_off_tail);
    println!("    \"c_dst_u32_len3\": {{\"size\": {}, \"align\": {}, \"tail_offset\": {}}},", size_of_val(c_dst_3), align_of_val(c_dst_3), c_dst_off_tail);
    println!("    \"rust_dst_u16_len2\": {{\"size\": {}, \"align\": {}, \"off_a\": {}, \"off_b\": {}, \"off_tail\": {}}},",
        size_of_val(rust_dst_2), align_of_val(rust_dst_2), rust_dst_off_a, rust_dst_off_b, rust_dst_off_tail);
    println!("    \"c_packed2_dst_u32_len1\": {{\"size\": {}, \"align\": {}, \"tail_offset\": {}}},",
        size_of_val(packed_dst_1), align_of_val(packed_dst_1), packed_dst_off_tail);
    println!("    \"outer_packed2_over_inner_c_dst_u32_len1\": {{\"size\": {}, \"align\": {}, \"off_inner\": {}, \"off_tail\": {}}},",
        size_of_val(nested_packed_dst), align_of_val(nested_packed_dst), nested_off_inner, nested_off_tail);
    println!("    \"c_dst_dyn_u8\": {{\"size\": {}, \"align\": {}, \"tail_offset\": {}}},", size_of_val(dyn_u8), align_of_val(dyn_u8), dyn_u8_off);
    println!("    \"c_dst_dyn_u64\": {{\"size\": {}, \"align\": {}, \"tail_offset\": {}}},", size_of_val(dyn_u64), align_of_val(dyn_u64), dyn_u64_off);
    println!("    \"c_dst_dyn_align32\": {{\"size\": {}, \"align\": {}, \"tail_offset\": {}}}", size_of_val(dyn_a32), align_of_val(dyn_a32), dyn_a32_off);
    println!("  }}");
    println!("}}");
}
