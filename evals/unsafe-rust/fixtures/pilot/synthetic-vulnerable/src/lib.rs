#![deny(unsafe_op_in_unsafe_fn)]

use core::{mem, ptr::NonNull};

pub fn decode_flag(raw: u8) -> bool {
    unsafe { mem::transmute(raw) }
}

pub trait AddressSource {
    fn address(&self) -> *const u8;
}

pub fn load_source<S: AddressSource>(source: &S) -> u8 {
    unsafe { source.address().read() }
}

pub struct ByteHandle {
    pub address: NonNull<u8>,
}

impl ByteHandle {
    pub fn load(&self) -> u8 {
        unsafe { self.address.as_ptr().read() }
    }
}

/// Returns `bytes[index]`.
///
/// # Safety
///
/// `index` must be less than `bytes.len()`.
pub unsafe fn item_unchecked(bytes: &[u8], index: usize) -> u8 {
    unsafe { *bytes.get_unchecked(0) }
}

macro_rules! make_indexer {
    ($name:ident) => {
        pub fn $name(bytes: &[u8], index: usize) -> u8 {
            debug_assert!(index < bytes.len());
            unsafe { *bytes.get_unchecked(index) }
        }
    };
}

make_indexer!(profile_index);

pub fn checked_first(bytes: &[u8]) -> Option<u8> {
    if bytes.is_empty() {
        return None;
    }
    // SAFETY: Since `u8` occupies one byte, every `[u8]` contains an element.
    Some(unsafe { *bytes.get_unchecked(0) })
}
