use std::mem::{align_of, offset_of, size_of, size_of_val};

#[allow(dead_code)]
struct Reordered {
    a: u8,
    b: u64,
    c: u16,
}

#[repr(C)]
#[allow(dead_code)]
struct CControl {
    a: u8,
    b: u64,
    c: u16,
}

#[repr(C)]
#[allow(dead_code)]
union CUnion {
    word: u64,
    bytes: [u8; 8],
}

#[allow(dead_code)]
enum Payload {
    Empty,
    Data(u64, u8),
    Pair(u16, u32),
}

trait Trait { fn value(&self) -> u32; }
struct Datum(u32);
impl Trait for Datum { fn value(&self) -> u32 { self.0 } }

fn main() {
    println!("Reordered size={} align={} offsets={},{},{}", size_of::<Reordered>(), align_of::<Reordered>(), offset_of!(Reordered,a), offset_of!(Reordered,b), offset_of!(Reordered,c));
    println!("CControl size={} align={} offsets={},{},{}", size_of::<CControl>(), align_of::<CControl>(), offset_of!(CControl,a), offset_of!(CControl,b), offset_of!(CControl,c));
    println!("CUnion size={} align={}", size_of::<CUnion>(), align_of::<CUnion>());
    println!("Payload size={} align={}", size_of::<Payload>(), align_of::<Payload>());
    println!("OptionRef size={} align={}", size_of::<Option<&u8>>(), align_of::<Option<&u8>>());
    println!("RefU8 size={} align={}", size_of::<&u8>(), align_of::<&u8>());
    println!("slice_pointer size={} align={}", size_of::<&[u16]>(), align_of::<&[u16]>());
    println!("str_pointer size={} align={}", size_of::<&str>(), align_of::<&str>());
    println!("trait_pointer size={} align={}", size_of::<&dyn Trait>(), align_of::<&dyn Trait>());
    let array = [1_u16, 2, 3];
    let slice: &[u16] = &array;
    let text: &str = "abc";
    let value = Datum(7);
    let object: &dyn Trait = &value;
    println!("slice_value size={} align={}", size_of_val(slice), std::mem::align_of_val(slice));
    println!("str_value size={} align={}", size_of_val(text), std::mem::align_of_val(text));
    println!("trait_value size={} align={} value={}", size_of_val(object), std::mem::align_of_val(object), object.value());
}
