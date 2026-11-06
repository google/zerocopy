#![allow(dead_code)]

use std::collections::BTreeMap;

type Long = BTreeMap<String, Vec<Option<(u64, u64, u64, u64, u64, u64, u64, u64)>>>;

fn wants_iterator<T: Iterator<Item = Long>>() {}

fn main() {
    let _: (u64, u64, u64, u64, u64, u64, u64, u64) =
        (1u8, 2u8, 3u8, 4u8, 5u8, 6u8, 7u8, 8u8);
    wants_iterator::<Vec<Long>>();
}
