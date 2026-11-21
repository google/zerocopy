//! Same size, different alignment: `[u8; 8]` (size 8, alignment 1) versus `u64`
//! (size 8, alignment 8).
fn main() {
    let raw = Box::into_raw(Box::new(7u64));
    let wrong: Box<[u8; 8]> = unsafe { Box::from_raw(raw as *mut [u8; 8]) };
    drop(wrong);
}
