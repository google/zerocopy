#![crate_type = "lib"]

/// ```hermes
/// ensures (h_size): ret.1.val = 1
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_u8() -> (usize, usize) {
    (core::mem::size_of::<u8>(), core::mem::align_of::<u8>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 1
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_i8() -> (usize, usize) {
    (core::mem::size_of::<i8>(), core::mem::align_of::<i8>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 1
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_bool() -> (usize, usize) {
    (core::mem::size_of::<bool>(), core::mem::align_of::<bool>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 4
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_char() -> (usize, usize) {
    (core::mem::size_of::<char>(), core::mem::align_of::<char>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 2
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_u16() -> (usize, usize) {
    (core::mem::size_of::<u16>(), core::mem::align_of::<u16>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 2
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_i16() -> (usize, usize) {
    (core::mem::size_of::<i16>(), core::mem::align_of::<i16>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 4
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_u32() -> (usize, usize) {
    (core::mem::size_of::<u32>(), core::mem::align_of::<u32>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 4
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_i32() -> (usize, usize) {
    (core::mem::size_of::<i32>(), core::mem::align_of::<i32>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 8
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_u64() -> (usize, usize) {
    (core::mem::size_of::<u64>(), core::mem::align_of::<u64>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 8
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_i64() -> (usize, usize) {
    (core::mem::size_of::<i64>(), core::mem::align_of::<i64>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 16
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_u128() -> (usize, usize) {
    (core::mem::size_of::<u128>(), core::mem::align_of::<u128>())
}

/// ```hermes
/// ensures (h_size): ret.1.val = 16
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_size):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_i128() -> (usize, usize) {
    (core::mem::size_of::<i128>(), core::mem::align_of::<i128>())
}

/// ```hermes
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_usize() -> (usize, usize) {
    (core::mem::size_of::<usize>(), core::mem::align_of::<usize>())
}

/// ```hermes
/// ensures (h_align_is_align): Hermes.IsAlignment ret.2.val
/// ensures (h_align_div): ret.2.val ∣ ret.1.val
/// proof (h_progress):
///   sorry
/// proof (h_align_is_align):
///   sorry
/// proof (h_align_div):
///   sorry
/// ```
pub fn test_isize() -> (usize, usize) {
    (core::mem::size_of::<isize>(), core::mem::align_of::<isize>())
}
