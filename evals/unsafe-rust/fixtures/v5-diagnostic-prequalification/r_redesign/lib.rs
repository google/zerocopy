#![allow(dead_code)]

pub trait Slot {
    fn index() -> usize;
}

pub struct Tail;

impl Slot for Tail {
    fn index() -> usize {
        1
    }
}

pub fn increment<S: Slot>(pair: &mut [u32; 2]) {
    let value = unsafe { pair.get_unchecked_mut(S::index()) };
    *value = value.wrapping_add(1);
}
