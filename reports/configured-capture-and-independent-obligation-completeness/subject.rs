// Illustrative source subject for the declared one-cell model. No importer proof.
// Caller must supply a live, aligned, readable/writable u32 place with access rights.
pub unsafe fn init_then_read(pointer: *mut u32) -> u32 {
    unsafe {
        pointer.write(7);
        pointer.read()
    }
}
