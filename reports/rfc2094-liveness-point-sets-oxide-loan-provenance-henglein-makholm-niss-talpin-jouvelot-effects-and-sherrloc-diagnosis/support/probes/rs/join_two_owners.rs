// A reference whose origin is the union of two loans at a join; one owner is then written.
pub fn join_two_owners(c: bool) -> u32 {
    let mut a = 1u32;
    let b = 2u32;
    let r = if c { &a } else { &b };
    a += 1;
    *r
}
