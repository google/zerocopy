#![allow(dead_code)]

pub fn total(values: &[u32]) -> u32 {
    let mut acc = 0u32;
    let mut ptr = values.as_ptr();
    let end = unsafe { ptr.add(values.len()) };

    while ptr != end {
        acc = acc.wrapping_add(unsafe { *ptr });
        ptr = unsafe { ptr.add(1) };
    }
    acc
}

