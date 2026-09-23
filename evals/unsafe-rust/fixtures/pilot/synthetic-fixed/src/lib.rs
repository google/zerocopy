#![deny(unsafe_op_in_unsafe_fn)]

pub fn decode_flag(raw: u8) -> bool {
    match raw {
        0 => false,
        1 => true,
        _ => panic!("invalid flag byte"),
    }
}

pub trait AddressSource {
    fn byte(&self) -> &u8;
}

pub fn load_source<S: AddressSource>(source: &S) -> u8 {
    *source.byte()
}

pub struct ByteHandle<'a> {
    address: &'a u8,
}

impl<'a> ByteHandle<'a> {
    pub fn new(address: &'a u8) -> Self {
        Self { address }
    }

    pub fn load(&self) -> u8 {
        *self.address
    }
}

/// Returns `bytes[index]`.
///
/// # Safety
///
/// `index` must be less than `bytes.len()`.
pub unsafe fn item_unchecked(bytes: &[u8], index: usize) -> u8 {
    unsafe { *bytes.get_unchecked(index) }
}

macro_rules! make_indexer {
    ($name:ident) => {
        pub fn $name(bytes: &[u8], index: usize) -> u8 {
            bytes[index]
        }
    };
}

make_indexer!(profile_index);

pub fn checked_first(bytes: &[u8]) -> Option<u8> {
    if bytes.is_empty() {
        return None;
    }
    // SAFETY: The preceding emptiness check establishes that index 0 is
    // in-bounds.
    Some(unsafe { *bytes.get_unchecked(0) })
}
