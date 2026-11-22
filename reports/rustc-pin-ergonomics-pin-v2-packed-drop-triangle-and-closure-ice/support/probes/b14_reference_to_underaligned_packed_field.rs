// Control (stable Rust, no feature gate): a reference to an under-aligned field of a packed
// struct is rejected, which is why Part A2 pins an alignment-1 leaf nested in an alignment-8
// field instead of the under-aligned field itself.
#![forbid(unsafe_code)]
#![crate_type = "lib"]

#[repr(packed)]
pub struct Packed(pub u8, pub u32);

pub fn f(p: &mut Packed) -> u32 {
    let Packed(_, ref mut b) = *p;
    *b
}
