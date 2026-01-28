use enum_dispatch::enum_dispatch;

use std::convert::TryInto;

#[enum_dispatch]
trait TestTrait {
    fn foo(&self) -> u8;
}

/// The `TryInto::Error` type should not cause conflicts with the variant name.
#[enum_dispatch(TestTrait)]
enum TestEnum {
    A,
    Error,
}

struct A;

impl TestTrait for A {
    fn foo(&self) -> u8 { 0 }
}

struct Error;

impl TestTrait for Error {
    fn foo(&self) -> u8 { 1 }
}

#[test]
fn main() {
    let te = TestEnum::from(Error);
    let _e: Error = te.try_into().unwrap();
}
