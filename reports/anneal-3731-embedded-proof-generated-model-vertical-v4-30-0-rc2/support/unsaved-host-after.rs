#![allow(dead_code)]
/// manually chosen obligation: obl_inc
pub fn inc(x: u32) -> u32 { x.wrapping_add(1) }
/// manually chosen obligation: obl_twice
pub fn twice(x: u32) -> u32 { inc(inc(x)) }
/// manually chosen obligation: obl_choose
pub fn choose(x: u32) -> u32 { if x == 0 { twice(1) } else { inc(x) } }

// anneal: theorem obl_inc : golden_vertical.inc 0#u32 = .ok 1#u32 := by
// anneal:   rfl
