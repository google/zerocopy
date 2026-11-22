#![allow(unused)]

pub unsafe trait MyUnsafe {}
pub struct S;
unsafe impl MyUnsafe for S where S: MyUnsafe {}

pub fn check_non_auto() {
    fn assert_u<T: MyUnsafe>() {}
    assert_u::<S>();
}
