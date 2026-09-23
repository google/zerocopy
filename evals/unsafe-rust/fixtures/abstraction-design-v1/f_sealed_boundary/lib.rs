#![allow(dead_code)]

pub trait Bytes {
    #[doc(hidden)]
    fn raw_parts(&self) -> (*const u8, usize);
}

pub struct Owned(Vec<u8>);

impl Bytes for Owned {
    fn raw_parts(&self) -> (*const u8, usize) {
        (self.0.as_ptr(), self.0.len())
    }
}

pub fn last<B: Bytes>(bytes: &B) -> Option<u8> {
    let (ptr, len) = bytes.raw_parts();
    (len != 0).then(|| unsafe { *ptr.add(len - 1) })
}

