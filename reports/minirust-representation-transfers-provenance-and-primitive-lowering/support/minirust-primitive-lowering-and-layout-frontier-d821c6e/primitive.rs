#![cfg_attr(target_arch = "wasm32", no_std)]
use core::hint::black_box as bb;
use core::mem::{align_of, size_of};
#[repr(C)] struct C { byte: u8, word: usize }
#[repr(C, packed)] struct Packed { byte: u8, word: usize }
#[derive(Clone, Copy)] union Wide { pointer: *const [u8] }

// Exports use scalar WebAssembly parameters/results only. There are no unsafe blocks.
#[unsafe(no_mangle)]
pub extern "C" fn primitive_case(i: u32) -> u32 {
    match i {
        0 => (bb(16777216.0f32) + bb(1.0)).to_bits(),
        1 => bb(-0.0f32).to_bits(),
        2 => (bb(f32::from_bits(1)) + bb(f32::from_bits(1))).to_bits(),
        3 => bb(f32::INFINITY) as u8 as u32,
        4 => bb(f32::NEG_INFINITY) as u8 as u32,
        5 => bb(f32::NAN) as u8 as u32,
        6 => bb(-1.9f32) as i32 as u32,
        7 => bb(257u16) as u8 as u32,
        8 => bb(255u8).wrapping_add(bb(1)) as u32,
        9 => bb(255u8).overflowing_add(bb(1)).1 as u32,
        10 => bb(1u8).wrapping_shl(bb(8)) as u32,
        11 => bb(1u8).checked_shl(bb(8)).is_none() as u32,
        12 => bb(i8::MIN).checked_div(bb(-1)).is_none() as u32,
        13 => (bb(f32::from_bits(0x7fc01234)) + bb(1.0)).is_nan() as u32,
        14 => (bb(f32::NAN) == bb(f32::NAN)) as u32,
        15 => f32::from_bits(bb(0x7fc01234)).to_bits(),
        16 => (bb(0.0f32) == bb(-0.0)) as u32,
        17 => (bb(f32::MAX) * bb(2.0)).is_infinite() as u32,
        18 => (bb(16777217u32) as f32).to_bits(),
        19 => size_of::<usize>() as u32,
        20 => size_of::<C>() as u32,
        21 => size_of::<Packed>() as u32,
        22 => size_of::<Option<core::num::NonZeroU8>>() as u32,
        23 => size_of::<Wide>() as u32,
        24 => { let mut b = [0,1,2,3,4,5]; b.copy_within(0..4, 2); (b == [0,1,0,1,2,3]) as u32 },
        25 => { let mut b = [0,1,2,3,4,5]; b.copy_within(2..6, 0); (b == [2,3,4,5,4,5]) as u32 },
        26 => { let mut b = [0,1,2,3,4,5]; b.copy_within(1..1, 5); (b == [0,1,2,3,4,5]) as u32 },
        27 => cfg!(target_has_atomic = "ptr") as u32,
        28 => cfg!(target_endian = "little") as u32,
        29 => align_of::<Wide>() as u32,
        30 => bb(2147483648.0f32) as i32 as u32,
        31 => (bb(f64::MAX) as f32).is_infinite() as u32,
        _ => 0,
    }
}
#[cfg(not(target_arch = "wasm32"))]
fn main() { println!("{:?}", (0..32).map(|i| primitive_case(i)).collect::<Vec<_>>()); }
#[cfg(target_arch = "wasm32")]
#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! { loop {} }
