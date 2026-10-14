#![crate_type = "lib"]

#[unsafe(no_mangle)]
pub extern "C" fn broken_safe_api(input: u8) -> u8 {
    if input == 0 {
        // This source function admits an ordinary safe call with input zero.
        unsafe { std::hint::unreachable_unchecked() }
    }
    7
}

#[unsafe(no_mangle)]
pub extern "C" fn always_seven(_input: u8) -> u8 {
    7
}
