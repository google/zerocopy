// Question: is an explicit `&mut v` written as a call argument two-phase?
pub fn f() -> Vec<usize> {
    let mut v: Vec<usize> = vec![1];
    Vec::push(&mut v, v.len());
    v
}
