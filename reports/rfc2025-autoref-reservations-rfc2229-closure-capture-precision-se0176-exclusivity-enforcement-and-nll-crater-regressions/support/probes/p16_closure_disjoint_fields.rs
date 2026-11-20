// RFC 2229 summary example: a closure borrows foo.b while foo.a is mutably borrowed.
// Expect: rejected in edition 2018, accepted in edition 2021.
pub struct Foo { a: u32, b: u32 }
fn somefunc(_a: &mut u32) {}
pub fn f(mut foo: Foo) {
    let a = &mut foo.a;
    let c = || foo.b + 1;
    let _ = c();
    somefunc(a);
}
