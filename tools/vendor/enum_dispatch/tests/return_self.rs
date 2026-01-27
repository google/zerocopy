use enum_dispatch::enum_dispatch;

#[enum_dispatch]
trait TestTrait {
    fn foo(&self) -> Self;
}

#[enum_dispatch(TestTrait)]
enum TestEnum {
    A,
    B,
}

struct A;

impl TestTrait for A {
    fn foo(&self) -> A {
        A
    }
}

struct B;

impl TestTrait for B {
    fn foo(&self) -> B {
        B
    }
}

#[test]
fn main() {
    let a = A;
    let e: TestEnum = a.into();
    let _: TestEnum = e.foo();
}
