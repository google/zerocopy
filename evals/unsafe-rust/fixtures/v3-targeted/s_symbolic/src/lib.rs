#![no_std]

/// Returns the contained byte, or zero when `value` is `None`.
pub fn value_or_zero(value: Option<u8>) -> u8 {
    if value.is_none() {
        return 0;
    }

    // SAFETY: The only `None` case returned above. Therefore `value` is
    // `Some` here, which is exactly `unwrap_unchecked`'s precondition.
    unsafe { value.unwrap_unchecked() }
}

