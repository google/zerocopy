// A field-less `#[repr(C)]` enum whose discriminants do not fit in C `int` or
// `unsigned int` (the shape of probe 14b in `support/crosscheck.rs`, without the
// `#[allow(repr_c_enums_larger_than_int)]` attribute).
// Expected outcome on the recorded compilers: compilation succeeds and emits the
// future-incompatibility warning `repr_c_enums_larger_than_int`.
// Compile from the package root with:
//   rustc --crate-type=lib support/repr_c_big_discriminant_lint.rs -o /tmp/big_discr.rlib

#[repr(C)]
pub enum FieldlessCBigDiscr {
    A = 0x1_0000_0000,
    B,
}
