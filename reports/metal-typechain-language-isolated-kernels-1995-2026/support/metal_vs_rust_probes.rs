// Empirical rustc probes for Sergio Benitez's "Rusty Types for Solid Safety" (PLAS 2016)
// Testing §3.2.2, §4.1, §4.2, §4.3, and §5 on modern rustc (NLL + Polonius).

#[derive(Debug)]
struct Q(i32);

#[derive(Debug)]
struct R(i32);

// 1. §4.3 Precision example:
// In 2016 lexical-lifetime Rust, this was rejected with:
//   "error: cannot assign to `x` because it is borrowed"
// Wait: what happens in modern NLL when `y` is STILL USED after `x = &mut b`?
// In Metal, `y` reborrows `*x` (location `l_a`), while `x`'s own pointer cell `l_x`
// remains owned & writeable by `x` (`owned(&mut Q(int@l_a)@l_x) = {l_x}`).
// Let's test whether modern NLL allows `x = &mut b` while `y` is still live and used afterward!
fn probe_sec4_3_reborrow_and_reassign() -> (i32, i32) {
    let mut a = Q(10);
    let mut b = Q(20);
    let mut x = &mut a;
    let y = &mut *x;
    x = &mut b;
    // Notice `y` is STILL LIVE here and mutates `a`, while `x` mutates `b`!
    y.0 += 1;
    x.0 += 2;
    (a.0, b.0)
}

// 2. §4.1 Drop (RAII) LIFO destruction order without regions vs with regions:
// Case A: Without Drop implementation (no destructor):
// Modern NLL allows `a = Parent(&p2)` even though `p2` is declared after `a`,
// PROVIDED `a` is not used after `p2` is dropped!
struct ParentNoDrop<'a>(&'a Q);

fn probe_sec4_1_no_drop_nll_accepts() -> i32 {
    let p1 = Q(1);
    let mut a = ParentNoDrop(&p1);
    let p2 = Q(2);
    a = ParentNoDrop(&p2);
    a.0 .0
    // `p2` is dropped before `a`, which is safe ONLY because `ParentNoDrop` has no Drop impl!
}

// Case B: With Drop implementation:
// `ParentWithDrop::drop(&mut self)` reads `self.0`. Because `p2` is declared after `a`,
// LIFO drop order drops `p2` BEFORE `a::drop(&mut a)` runs!
// In region-less Metal (§4.1), `a = Parent(&p2)` would be accepted by (ST1), causing a
// use-after-free in `Parent::drop`! Rust rejects Case B via region outlives constraints (`'a: scope(a)`).
#[cfg(feature = "fail_drop_lifo")]
struct ParentWithDrop<'a>(&'a Q);
#[cfg(feature = "fail_drop_lifo")]
impl<'a> Drop for ParentWithDrop<'a> {
    fn drop(&mut self) {
        println!("Dropping parent pointing to {}", (self.0).0);
    }
}
#[cfg(feature = "fail_drop_lifo")]
fn probe_sec4_1_with_drop_rejects() {
    let p1 = Q(1);
    let mut a = ParentWithDrop(&p1);
    let p2 = Q(2);
    a = ParentWithDrop(&p2);
}

// 3. §3.2.2 & §4.2 Function signature Outliving-Borrow (OL) analysis:
// Without regions (§3.2.2), `fn f(a: &mut Wrap<&R>, b: &R)` treats `b` as potentially stored into `*a`,
// so `b` is consumed (cannot be restored after the call).
// With distinct regions `'a` and `'b` (§4.2), `b` cannot be stored into `a`, so `b` remains usable.
struct Wrap<'a>(&'a R);

fn sig_distinct_regions<'a, 'b>(_a: &mut Wrap<'a>, _b: &'b R) {}

fn probe_sec4_2_distinct_regions() -> i32 {
    let r1 = R(100);
    let r2 = R(200);
    let mut w = Wrap(&r1);
    let b = &r2;
    sig_distinct_regions(&mut w, b);
    // `b` is still usable and `r2` can even be read through `b`
    b.0 + w.0 .0
}

fn main() {
    let (a_val, b_val) = probe_sec4_3_reborrow_and_reassign();
    assert_eq!((a_val, b_val), (11, 22));
    let nd = probe_sec4_1_no_drop_nll_accepts();
    assert_eq!(nd, 2);
    let dr = probe_sec4_2_distinct_regions();
    assert_eq!(dr, 300);
    println!("All positive probes passed: sec4_3={:?}, sec4_1_no_drop={}, sec4_2={}", (a_val, b_val), nd, dr);
}
