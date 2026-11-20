// Adapted from the "unnecessary error" example shipped with the Oxide model
// (reducer/examples/unnecessary_error.rs): a subset relation created on one
// branch meets a loan created on a later branch.
fn random_bool() -> bool { std::hint::black_box(true) }
pub fn unnecessary_error() {
    let m: u32 = 0;
    let n: u32 = 1;
    let mut x: (&u32,) = (&m,);
    let mut y: (&u32,) = (&n,);
    let mut z: u32 = 2;
    if random_bool() {
        y.0 = x.0; // 'x flows into 'y
    }
    if random_bool() {
        x.0 = &z; // new loan of z flows into 'x
        drop(x.0);
    }
    z += 1; // is the loan of z still live via 'y?
    drop(y.0);
}
