extern crate zerocopy_derive;
use zerocopy_derive::inline_assert_size_eq;

#[inline_assert_size_eq(1)]
struct TestSizeNeqStruct {
    i: i32,
}

fn main() {}
