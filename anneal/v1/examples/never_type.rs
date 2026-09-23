/// ```lean, anneal, spec
/// ensures: False
/// ```
pub fn crashes(x: u32) -> ! {
    if x > 0 {
        panic!("nonzero");
    } else {
        panic!("zero");
    }
}

pub fn may_crash(x: u32) -> u32 {
    if x == 0 { crashes(x) } else { x }
}

fn main() {}
