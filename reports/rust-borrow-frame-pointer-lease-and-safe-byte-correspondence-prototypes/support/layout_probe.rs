use std::mem::{align_of, size_of};
use std::num::NonZeroU8;

#[repr(C)]
struct Padded { byte: u8, word: u32 }
#[repr(C)]
struct Nested { tag: u8, inner: Padded }
#[repr(C, packed)]
struct Packed { byte: u8, word: u32 }
#[repr(align(16))]
struct AlignedUnit;

fn show<T>(name: &str) {
    println!("{name}:size={},align={}", size_of::<T>(), align_of::<T>());
}
fn main() {
    show::<u64>("u64");
    show::<bool>("bool");
    show::<[bool; 3]>("bool_array_3");
    show::<[(); 3]>("unit_array_3");
    show::<Padded>("repr_c_padded");
    show::<Nested>("repr_c_nested");
    show::<Packed>("repr_c_packed");
    show::<AlignedUnit>("aligned_unit");
    show::<Option<NonZeroU8>>("option_nonzero_u8");
    show::<usize>("usize");
    println!("padded_offsets={},{}", std::mem::offset_of!(Padded, byte), std::mem::offset_of!(Padded, word));
    println!("nested_inner_offset={}", std::mem::offset_of!(Nested, inner));
    println!("packed_word_offset={}", std::mem::offset_of!(Packed, word));
    println!("checked_add_overflow={:?}", usize::MAX.checked_add(1));
    println!("wrapping_add_overflow={}", usize::MAX.wrapping_add(1));
}
