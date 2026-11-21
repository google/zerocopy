#![no_std]

#[unsafe(no_mangle)]
pub extern "C" fn probe_u128_div(a: u128, b: u128) -> u128 {
    a / b
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_u128_rem(a: u128, b: u128) -> u128 {
    a % b
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_i128_div(a: i128, b: i128) -> i128 {
    a / b
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_u128_mul(a: u128, b: u128) -> u128 {
    a.wrapping_mul(b)
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_u128_shl(a: u128, s: u32) -> u128 {
    a.wrapping_shl(s)
}

#[unsafe(no_mangle)]
pub extern "C" fn probe_u128_lshr(a: u128, s: u32) -> u128 {
    a.wrapping_shr(s)
}
