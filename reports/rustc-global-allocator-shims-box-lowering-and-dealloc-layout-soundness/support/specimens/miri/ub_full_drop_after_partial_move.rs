//! One field is moved out of the boxed pair and dropped by its new owner; then the whole pair is
//! dropped in place anyway. The moved-out field's destructor runs a second time.
#![allow(dead_code)]
struct Pair {
    first: Box<u64>,
    second: Box<u64>,
}

fn main() {
    let b = Box::new(Pair { first: Box::new(1), second: Box::new(2) });
    let raw: *mut Pair = Box::into_raw(b);
    unsafe {
        let first = std::ptr::read(std::ptr::addr_of!((*raw).first));
        drop(first);
        // Wrong: a full drop of `Pair`. Correct code would drop only `(*raw).second`.
        std::ptr::drop_in_place(raw);
        std::alloc::dealloc(raw as *mut u8, std::alloc::Layout::new::<Pair>());
    }
}
