use zerocopy_derive::*;

// The only valid value of this type are the bytes `0xC0C0`.
#[derive(TryFromBytes, KnownLayout, Immutable)]
#[repr(u16)]
pub enum C0C0 {
    _XC0C0 = 0xC0C0,
}

#[derive(FromBytes, KnownLayout, Immutable)]
#[repr(C, align(2))]
pub struct Packet<Magic> {
    magic_number: Magic,
    mug_size: u8,
    temperature: u8,
    marshmallows: [u8; 2],
}

/// A packet begining with the magic number `0xC0C0`.
pub type CocoPacket = Packet<C0C0>;

/// A packet beginning with any two initialized bytes.
pub type LocoPacket = Packet<[u8; 2]>;
