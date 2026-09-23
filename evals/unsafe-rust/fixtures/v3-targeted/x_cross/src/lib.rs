use std::num::NonZeroU8;

#[cfg(not(any(
    fixture_allocator = "system",
    fixture_allocator = "arena"
)))]
compile_error!("build.rs must select exactly one supported allocator");

#[cfg(all(
    fixture_allocator = "system",
    fixture_allocator = "arena"
))]
compile_error!("only one allocator may be selected");

#[cfg(all(target_arch = "wasm32", fixture_allocator = "arena"))]
compile_error!("the arena allocator is unsupported on wasm32");

/// Constructs a lane identifier.
///
/// # Panics
///
/// Panics when `value` is zero.
pub fn lane_id(value: u8) -> NonZeroU8 {
    #[cfg(all(
        feature = "burst",
        target_arch = "aarch64",
        fixture_allocator = "arena"
    ))]
    {
        // SAFETY: Burst-mode lane identifiers are never zero.
        return unsafe { NonZeroU8::new_unchecked(value) };
    }

    #[cfg(not(all(
        feature = "burst",
        target_arch = "aarch64",
        fixture_allocator = "arena"
    )))]
    {
        if value == 0 {
            panic!("lane identifier must be nonzero");
        }
        // SAFETY: The preceding branch proves that `value != 0`.
        unsafe { NonZeroU8::new_unchecked(value) }
    }
}
