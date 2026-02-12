use zerocopy::{TryFromBytes, try_transmute_ref};
use zerocopy_derive::*;

// The only valid value of this type is the byte `0xC0`
#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(u8)]
enum C0 { xC0 = 0xC0 }

// The only valid value of this type is the bytes `0xC0C0`.
#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(C)]
struct C0C0(C0, C0);

#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(C)]
pub struct Packet {
    magic_number: C0C0,
    mug_size: u8,
    temperature: u8,
    marshmallows: [[u8; 2]],
}