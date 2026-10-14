use crate::Harness;
use std::mem::{align_of, align_of_val, offset_of, size_of, size_of_val};
use std::num::NonZeroU16;

#[repr(C)]
struct CRecord { tag: u8, word: u32, tail: u16 }

#[repr(C)]
struct Tail<T: ?Sized> { head: u16, payload: T }

#[repr(u8)]
#[derive(Clone, Copy)]
enum Tag { Zero = 0, Seven = 7, Max = 255 }

enum Payload { Byte(u8), Word(u32) }

trait Measure { fn value(&self) -> u64; }
#[repr(C)]
struct Pair { left: u32, right: u16 }
struct Byte(u8);
impl Measure for Pair { fn value(&self) -> u64 { u64::from(self.left) + u64::from(self.right) } }
impl Measure for Byte { fn value(&self) -> u64 { u64::from(self.0) * 2 } }

fn round_up(n: usize, align: usize) -> usize {
    // All callers here use tiny constants and nonzero Rust type alignments.
    ((n + align - 1) / align) * align
}

fn observe_dyn(h: &mut Harness, name: &str, value: &dyn Measure, expected: u64, size: usize, align: usize) {
    println!("OBS layout.dyn.{}.size={} align={} value={}", name, size_of_val(value), align_of_val(value), value.value());
    h.check(&format!("layout.dyn.{}.dispatch", name), value.value() == expected);
    h.check(&format!("layout.dyn.{}.pointee_layout", name), size_of_val(value) == size && align_of_val(value) == align);
}

pub fn run(h: &mut Harness) {
    let c = CRecord { tag: 0x12, word: 0x3456_789a, tail: 0xbcde };
    println!("OBS layout.CRecord.size={} align={} offsets={},{},{}", size_of::<CRecord>(), align_of::<CRecord>(), offset_of!(CRecord, tag), offset_of!(CRecord, word), offset_of!(CRecord, tail));
    let align = align_of::<u8>().max(align_of::<u32>()).max(align_of::<u16>());
    let word_offset = round_up(size_of::<u8>(), align_of::<u32>());
    let tail_offset = round_up(word_offset + size_of::<u32>(), align_of::<u16>());
    let size = round_up(tail_offset + size_of::<u16>(), align);
    h.check("layout.repr_c_formula", offset_of!(CRecord, tag) == 0 && offset_of!(CRecord, word) == word_offset && offset_of!(CRecord, tail) == tail_offset && size_of::<CRecord>() == size && align_of::<CRecord>() == align);
    h.check("layout.fields_preserved", c.tag == 0x12 && c.word == 0x3456_789a && c.tail == 0xbcde);
    // Do not read struct padding. Native byte order is observed on scalars only.
    println!("OBS layout.CRecord.word_native_bytes={:?}", c.word.to_ne_bytes());

    let array = [0x1122_u16, 0x3344, 0x5566];
    let slice: &[u16] = &array;
    let middle: &[u16] = &slice[1..3];
    println!("OBS layout.array.size={} align={}", size_of_val(&array), align_of_val(&array));
    println!("OBS layout.slice.reference_size={} reference_align={} pointee_size={} pointee_align={} len={}", size_of::<&[u16]>(), align_of::<&[u16]>(), size_of_val(slice), align_of_val(slice), slice.len());
    h.check("layout.array_stride", size_of::<[u16; 3]>() == 3 * size_of::<u16>() && align_of::<[u16; 3]>() == align_of::<u16>());
    h.check("layout.slice_metadata_semantics", slice.len() == 3 && size_of_val(slice) == 3 * size_of::<u16>() && middle == [0x3344, 0x5566]);
    let tail = Tail { head: 17, payload: [11_u32, 22, 33] };
    let dst_tail: &Tail<[u32]> = &tail;
    println!("OBS layout.Tail.size={} align={} payload_offset={} unsized_size={} unsized_align={} len={}", size_of_val(&tail), align_of_val(&tail), offset_of!(Tail<[u32; 3]>, payload), size_of_val(dst_tail), align_of_val(dst_tail), dst_tail.payload.len());
    h.check("layout.unsized_tail_semantics", dst_tail.head == 17 && dst_tail.payload == [11, 22, 33] && size_of_val(dst_tail) == size_of_val(&tail) && align_of_val(dst_tail) == align_of_val(&tail));

    println!("OBS layout.enum.tag_size={} tag_align={} payload_size={} payload_align={}", size_of::<Tag>(), align_of::<Tag>(), size_of::<Payload>(), align_of::<Payload>());
    h.check("layout.repr_u8_fieldless_enum", size_of::<Tag>() == 1 && align_of::<Tag>() == 1 && Tag::Zero as u8 == 0 && Tag::Seven as u8 == 7 && Tag::Max as u8 == 255);
    let variants = [Payload::Byte(17), Payload::Word(0x1234_5678)];
    let values: Vec<u32> = variants.iter().map(|p| match p { Payload::Byte(x) => u32::from(*x), Payload::Word(x) => *x }).collect();
    h.check("layout.data_enum_match", values == [17, 0x1234_5678]);
    let nonzero = NonZeroU16::new(7).unwrap();
    let some = Some(nonzero);
    let none: Option<NonZeroU16> = None;
    let byte = 41_u8;
    let some_ref = Some(&byte);
    println!("OBS layout.niche.nonzero_option_size={} align={} reference_option_size={} align={} bool_option_size={}", size_of::<Option<NonZeroU16>>(), align_of::<Option<NonZeroU16>>(), size_of::<Option<&u8>>(), align_of::<Option<&u8>>(), size_of::<Option<bool>>());
    h.check("layout.documented_niche_sizes", size_of::<Option<NonZeroU16>>() == size_of::<NonZeroU16>() && align_of::<Option<NonZeroU16>>() == align_of::<NonZeroU16>() && size_of::<Option<&u8>>() == size_of::<&u8>() && align_of::<Option<&u8>>() == align_of::<&u8>());
    h.check("layout.niche_values", some.map(NonZeroU16::get) == Some(7) && none.is_none() && some_ref.copied() == Some(41));

    let pair = Pair { left: 1000, right: 7 };
    let byte = Byte(9);
    println!("OBS layout.trait_object.reference_size={} reference_align={}", size_of::<&dyn Measure>(), align_of::<&dyn Measure>());
    observe_dyn(h, "Pair", &pair, 1007, size_of::<Pair>(), align_of::<Pair>());
    observe_dyn(h, "Byte", &byte, 18, size_of::<Byte>(), align_of::<Byte>());
    // No vtable slots, object bytes, addresses, or ABI-unstable dispatch encodings are inspected.
}
