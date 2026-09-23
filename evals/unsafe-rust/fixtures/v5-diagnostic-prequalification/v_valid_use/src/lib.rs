#![allow(dead_code)]

/// Selects an element of a two-element array.
///
/// # Safety
///
/// Every call to `index` for an implementing type must return a value less
/// than `2`.
pub unsafe trait Slot {
    fn index() -> usize;
}

/// Returns the element selected by `S`.
pub fn choose<S: Slot>(pair: &[u8; 2]) -> u8 {
    // SAFETY: Implementors of `Slot` promise that this index is less than 2.
    unsafe { *pair.get_unchecked(S::index()) }
}

pub struct Anchor;

unsafe impl Slot for Anchor {
    fn index() -> usize {
        2
    }
}

/// Returns the element selected by the crate's `Anchor` type.
pub fn owned(pair: &[u8; 2]) -> u8 {
    choose::<Anchor>(pair)
}
