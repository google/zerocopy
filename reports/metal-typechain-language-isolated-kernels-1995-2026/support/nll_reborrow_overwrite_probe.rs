// Testing why NLL accepts or rejects overwriting `x` while `*x` is reborrowed in `y`
struct Q(i32);

fn case1_reborrow_mut_direct() -> i32 {
    let mut a = Q(10);
    let mut b = Q(20);
    let mut x = &mut a;
    let y = &mut *x;
    x = &mut b;
    y.0 + x.0
}

fn case2_reborrow_via_fn<'a>(r: &'a mut Q) -> &'a mut i32 {
    &mut r.0
}

fn test_case2() -> i32 {
    let mut a = Q(10);
    let mut b = Q(20);
    let mut x = &mut a;
    let y = case2_reborrow_via_fn(x);
    x = &mut b;
    *y + x.0
}

struct Holder<'a>(&'a mut Q);

fn test_case3_struct_wrapping_mut_ref() -> i32 {
    let mut a = Q(10);
    let mut b = Q(20);
    let mut h = Holder(&mut a);
    let y = &mut *h.0;
    h = Holder(&mut b);
    y.0 + h.0 .0
}

fn main() {
    println!("{} {} {}", case1_reborrow_mut_direct(), test_case2(), test_case3_struct_wrapping_mut_ref());
}
