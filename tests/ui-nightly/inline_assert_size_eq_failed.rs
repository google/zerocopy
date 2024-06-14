extern crate zerocopy;
extern crate zerocopy_derive;
use zerocopy::*;
use zerocopy_derive::assert_size_eq;

#[assert_size_eq(1)]
struct TestSizeNeqStruct {
    i: i32,
}

fn main() {}
