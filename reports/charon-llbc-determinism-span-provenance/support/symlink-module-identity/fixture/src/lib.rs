#[path = "left/common.rs"]
pub mod left;
#[path = "right/common.rs"]
pub mod right;

pub fn combine(x: u32) -> u32 {
    left::step(x).wrapping_add(right::step(x))
}
