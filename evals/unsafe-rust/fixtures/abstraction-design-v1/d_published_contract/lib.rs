#![allow(dead_code)]

pub unsafe trait Block {
    /// A nonzero power of two.
    const ALIGN: usize;

    /// During the borrow, the result is non-null, `ALIGN`-aligned, and readable
    /// for 16 bytes.
    fn base(&self) -> *const u8;
}

#[repr(C, align(16))]
pub struct Page([u8; 16]);

unsafe impl Block for Page {
    const ALIGN: usize = 16;

    fn base(&self) -> *const u8 {
        self.0.as_ptr()
    }
}

pub fn first<B: Block>(block: &B) -> u8 {
    unsafe { *block.base() }
}
