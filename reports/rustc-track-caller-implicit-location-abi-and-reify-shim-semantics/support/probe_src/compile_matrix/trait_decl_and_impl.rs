// Accepted: the attribute on a bodiless trait method, on a provided method, and on an impl method.
trait T {
    #[track_caller]
    fn a(&self);
    #[track_caller]
    fn b(&self) {}
    fn c(&self);
}
struct S;
impl T for S {
    fn a(&self) {}
    #[track_caller]
    fn c(&self) {}
}
fn main() {
    S.a();
    S.b();
    S.c();
}
