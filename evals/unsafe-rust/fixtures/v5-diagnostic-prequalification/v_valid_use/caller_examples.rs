use valid_use_target::{choose, Slot};

struct East;

unsafe impl Slot for East {
    fn index() -> usize {
        2
    }
}

pub fn example_east() -> u8 {
    choose::<East>(&[11, 29])
}

struct West;

unsafe impl Slot for West {
    fn index() -> usize {
        1
    }
}

pub fn example_west() -> u8 {
    choose::<West>(&[11, 29])
}
