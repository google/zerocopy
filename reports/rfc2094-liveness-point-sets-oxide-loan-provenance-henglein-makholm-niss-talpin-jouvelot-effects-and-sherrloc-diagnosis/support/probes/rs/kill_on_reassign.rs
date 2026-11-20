// Adapted from reducer/examples/kill_rules.rs in the Oxide model: assignment kills a reborrow loan.
pub fn kill_rules() {
    let mut m: u32 = 0;
    let mut n: u32 = 0;
    let mut q: &mut u32 = &mut m;
    let r: &mut u32 = &mut *q; // loan of *q
    q = &mut n;                // overwriting q kills the loan of *q
    *q += 1;
    *r += 1;
}
