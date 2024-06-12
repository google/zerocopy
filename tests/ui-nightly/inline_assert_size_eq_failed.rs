extern crate zerocopy;
extern crate zerocopy_derive;
use zerocopy::*;
use zerocopy_derive::assert_size_eq_val;

#[assert_size_eq_val(1)]
struct TestSizeNeqStruct {
    i: i32,
}

fn main() {}
