//! A block allocated for `u64` (size 8, alignment 8) is given back through a `Box<u32>`
//! (size 4, alignment 4): the `Box` destructor derives the layout from the pointee type.
fn main() {
    let raw = Box::into_raw(Box::new(7u64));
    let wrong: Box<u32> = unsafe { Box::from_raw(raw as *mut u32) };
    drop(wrong);
}
