use core::convert::TryInto;
use enum_dispatch::enum_dispatch;

pub struct A;
pub struct B;

impl A {
    fn describe(&self) -> &str {
        "A - base impl"
    }
}

#[enum_dispatch]
pub enum Traited {
    A,
    B,
}

#[enum_dispatch(Traited)]
trait TestTrait {
    fn describe(&self) -> &str;
}

impl TestTrait for A {
    fn describe(&self) -> &str {
        "A - TestTrait"
    }
}

impl TestTrait for B {
    fn describe(&self) -> &str {
        "B - TestTrait"
    }
}

#[enum_dispatch(Traited)]
trait Descriptive {
    fn describe(&self) -> &str;
}

impl Descriptive for A {
    fn describe(&self) -> &str {
        "A - Descriptive"
    }
}

impl Descriptive for B {
    fn describe(&self) -> &str {
        "B - Descriptive"
    }
}

#[test]
fn main() {
    let a = Traited::from(A);
    let b = Traited::from(B);

    assert_eq!(TestTrait::describe(&a), "A - TestTrait");
    assert_eq!(TestTrait::describe(&b), "B - TestTrait");
    assert_eq!(Descriptive::describe(&a), "A - Descriptive");
    assert_eq!(Descriptive::describe(&b), "B - Descriptive");

    let a: A = a.try_into().unwrap();
    assert_eq!(a.describe(), "A - base impl");
    assert_eq!(TestTrait::describe(&a), "A - TestTrait");
    assert_eq!(Descriptive::describe(&a), "A - Descriptive");
}
