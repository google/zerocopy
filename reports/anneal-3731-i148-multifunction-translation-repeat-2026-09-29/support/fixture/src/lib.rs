pub struct Pair {
    pub left: u32,
    pub right: u32,
}

pub fn add_one(x: u32) -> u32 {
    x + 1
}

pub fn choose(flag: bool, x: u32, y: u32) -> u32 {
    if flag { x } else { y }
}

pub fn pair_sum(pair: Pair) -> u32 {
    pair.left + pair.right
}

pub fn make_pair(x: u32, y: u32) -> Pair {
    Pair { left: x, right: y }
}

pub fn combine(flag: bool, x: u32, y: u32) -> u32 {
    let p = make_pair(x, y);
    add_one(choose(flag, p.left, p.right))
}
