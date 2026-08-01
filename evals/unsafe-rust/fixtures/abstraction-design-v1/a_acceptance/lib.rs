#![allow(dead_code)]

pub unsafe trait Piece {
    type Owner;
    type Item;

    /// The name of a direct declared field of `Owner` whose type is `Item`.
    const FIELD: &'static str;

    /// Returns a pointer to that direct declared field.
    ///
    /// # Safety
    ///
    /// `owner` must identify a live, uniquely borrowed `Owner` for the call.
    unsafe fn project(owner: *mut Self::Owner) -> *mut Self::Item;
}

pub struct Pair(pub [u32; 2]);
pub struct Tail;

unsafe impl Piece for Tail {
    type Owner = Pair;
    type Item = u32;
    const FIELD: &'static str = "tail";

    unsafe fn project(owner: *mut Pair) -> *mut u32 {
        unsafe { core::ptr::addr_of_mut!((*owner).0[1]) }
    }
}

pub fn increment_tail(pair: &mut Pair) {
    let value = unsafe { &mut *Tail::project(pair) };
    *value = value.wrapping_add(1);
}

