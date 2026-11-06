#![allow(dead_code)]

pub fn checked_add(x: u32, y: u32) -> Option<u32> {
    x.checked_add(y)
}

pub fn choose(flag: bool, left: u32, right: u32) -> u32 {
    if flag { left } else { right }
}

pub fn bump(value: &mut u32) {
    *value = value.wrapping_add(1);
}
