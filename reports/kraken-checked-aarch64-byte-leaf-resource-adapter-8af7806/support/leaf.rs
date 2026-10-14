use std::arch::naked_asm;
use std::hint::black_box;
use std::process::ExitCode;

// Safety contract: p points to one initialized, readable byte for this call.
// No pointer constructed by the test points outside a live allocation.
#[unsafe(naked)]
#[unsafe(no_mangle)]
pub unsafe extern "C" fn read_byte_leaf(_p: *const u8) -> u8 {
    naked_asm!("ldrb w0, [x0]", "ret");
}

#[inline(never)]
#[unsafe(no_mangle)]
pub fn checked_read(byte: &u8) -> u8 {
    // A shared reference supplies a live initialized byte for this bounded call.
    unsafe { read_byte_leaf(byte as *const u8) }
}

#[inline(never)]
pub fn rust_read(byte: &u8) -> u8 { *byte }

fn main() -> ExitCode {
    let mut count = 0u64;
    let mut checksum = 0u64;
    for value in 0u8..=255 {
        for offset in 0..65 {
            let mut frame = [0xa5u8; 65];
            frame[offset] = value;
            let before = frame;
            let byte = black_box(&frame[offset]);
            let actual = checked_read(byte);
            let expected = rust_read(byte);
            if actual != value || actual != expected || frame != before {
                eprintln!("disagreement value={value} offset={offset}");
                return ExitCode::FAILURE;
            }
            checksum = checksum.wrapping_mul(0x100000001b3).wrapping_add(actual as u64);
            count += 1;
        }
    }
    println!("{{\"cases\":{count},\"checksum\":\"{checksum:016x}\",\"valid_reference_only\":true}}");
    ExitCode::SUCCESS
}
