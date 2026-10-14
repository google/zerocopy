trait Family { type Borrow<'a> where Self: 'a; }
fn object(_: &dyn Family<Borrow<'static> = &'static [u8]>) {}
fn main() {}
