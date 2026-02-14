
pub fn swap(a: &mut u32, b: &mut u32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}

pub fn swap_reordered(b: &mut u32, a: &mut u32) {
    let tmp = *a;
    *a = *b;
    *b = tmp;
}
