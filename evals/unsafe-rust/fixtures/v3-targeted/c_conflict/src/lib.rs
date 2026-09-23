#![no_std]

#[cfg(all(feature = "turbo", target_arch = "wasm32"))]
compile_error!("the turbo feature is not supported on wasm32");

/// Returns the contained byte, or zero when `value` is `None`.
#[cfg(not(feature = "turbo"))]
pub fn value_or_zero(value: Option<u8>) -> u8 {
    value.unwrap_or(0)
}

/// Returns the contained byte, or zero when `value` is `None`.
#[cfg(feature = "turbo")]
pub fn value_or_zero(value: Option<u8>) -> u8 {
    if value.is_none() {
        return 0;
    }

    // SAFETY: The `None` case returned above, so this value is `Some`.
    unsafe { value.unwrap_unchecked() }
}

