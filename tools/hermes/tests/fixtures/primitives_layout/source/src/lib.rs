#![crate_type = "lib"]

/// ```hermes
/// ensures ret.1.val = 1 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_u8
///   simp
/// ```
pub fn test_u8() -> (usize, usize) {
    (core::mem::size_of::<u8>(), core::mem::align_of::<u8>())
}

/// ```hermes
/// ensures ret.1.val = 1 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_i8
///   simp
/// ```
pub fn test_i8() -> (usize, usize) {
    (core::mem::size_of::<i8>(), core::mem::align_of::<i8>())
}

/// ```hermes
/// ensures ret.1.val = 1 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_bool
///   simp
/// ```
pub fn test_bool() -> (usize, usize) {
    (core::mem::size_of::<bool>(), core::mem::align_of::<bool>())
}

/// ```hermes
/// ensures ret.1.val = 4 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_char
///   simp
/// ```
pub fn test_char() -> (usize, usize) {
    (core::mem::size_of::<char>(), core::mem::align_of::<char>())
}

/// ```hermes
/// ensures ret.1.val = 2 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_u16
///   simp
/// ```
pub fn test_u16() -> (usize, usize) {
    (core::mem::size_of::<u16>(), core::mem::align_of::<u16>())
}

/// ```hermes
/// ensures ret.1.val = 2 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_i16
///   simp
/// ```
pub fn test_i16() -> (usize, usize) {
    (core::mem::size_of::<i16>(), core::mem::align_of::<i16>())
}

/// ```hermes
/// ensures ret.1.val = 4 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_u32
///   simp
/// ```
pub fn test_u32() -> (usize, usize) {
    (core::mem::size_of::<u32>(), core::mem::align_of::<u32>())
}

/// ```hermes
/// ensures ret.1.val = 4 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_i32
///   simp
/// ```
pub fn test_i32() -> (usize, usize) {
    (core::mem::size_of::<i32>(), core::mem::align_of::<i32>())
}

/// ```hermes
/// ensures ret.1.val = 8 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_u64
///   simp
/// ```
pub fn test_u64() -> (usize, usize) {
    (core::mem::size_of::<u64>(), core::mem::align_of::<u64>())
}

/// ```hermes
/// ensures ret.1.val = 8 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_i64
///   simp
/// ```
pub fn test_i64() -> (usize, usize) {
    (core::mem::size_of::<i64>(), core::mem::align_of::<i64>())
}

/// ```hermes
/// ensures ret.1.val = 16 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_u128
///   simp
/// ```
pub fn test_u128() -> (usize, usize) {
    (core::mem::size_of::<u128>(), core::mem::align_of::<u128>())
}

/// ```hermes
/// ensures ret.1.val = 16 /\ Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_i128
///   simp
/// ```
pub fn test_i128() -> (usize, usize) {
    (core::mem::size_of::<i128>(), core::mem::align_of::<i128>())
}

/// ```hermes
/// ensures Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_usize
///   simp
/// ```
pub fn test_usize() -> (usize, usize) {
    (core::mem::size_of::<usize>(), core::mem::align_of::<usize>())
}

/// ```hermes
/// ensures Hermes.IsAlignment ret.2.val /\ ret.2.val ∣ ret.1.val
/// proof
///   unfold test_isize
///   simp
/// ```
pub fn test_isize() -> (usize, usize) {
    (core::mem::size_of::<isize>(), core::mem::align_of::<isize>())
}
