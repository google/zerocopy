// Zero-variant enums carrying `#[repr(C)]` or a primitive representation.
// Expected outcome: compilation fails, with one error E0084
// ("unsupported representation for zero-variant enum") per enum.
// Compile from the package root with:
//   rustc --crate-type=lib support/e0084_zero_variant_enums.rs -o /tmp/e0084.rlib

#[repr(C)]
pub enum ZeroVariantC {}

#[repr(u8)]
pub enum ZeroVariantU8 {}

#[repr(i32)]
pub enum ZeroVariantI32 {}

#[repr(usize)]
pub enum ZeroVariantUsize {}
