// The conflicting loan is created on only one branch; the use is after the join.
pub fn one_branch(c: bool) -> u32 {
    let mut v = vec![1u32];
    let zero = 0u32;
    let r: &u32;
    if c { r = &v[0]; } else { r = &zero; }
    v.push(2);
    *r
}
