// Probing exact NLL shallow-write vs deep-prefix rules in rustc 1.101.0-nightly
struct Q(i32);

// Wait: does NLL accept shared reborrow `let y = &*x; x = &mut b; y.0 + x.0`?
fn shared_reborrow_then_reassign() -> i32 {
    let mut a = Q(10);
    let mut b = Q(20);
    let mut x = &mut a;
    let y = &*x;
    x = &mut b;
    y.0 + x.0
}

// What if we read `x.0` BEFORE reassigning `x = &mut b`, while `y` is live?
#[cfg(feature = "fail_read_x_while_y_live")]
fn read_x_while_y_live() -> i32 {
    let mut a = Q(10);
    let mut x = &mut a;
    let y = &mut *x;
    let v = x.0; // ERROR: cannot use `x.0` because it was mutably borrowed
    y.0 + v
}

// What if `x` is `Box<Q>` (owns `*x`) and we reassign `x` while `y = &mut *x` is live?
#[cfg(feature = "fail_box_reassign")]
fn box_reassign_while_borrowed() -> i32 {
    let mut x = Box::new(Q(10));
    let y = &mut *x;
    x = Box::new(Q(20)); // ERROR: cannot assign to `x` because it is borrowed
    y.0 + x.0
}

fn main() {
    println!("shared_reborrow_then_reassign = {}", shared_reborrow_then_reassign());
}
