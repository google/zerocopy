#![allow(unused)]
extern crate zerocopy_derive;
extern crate static_assertions;
use zerocopy_derive::*;
use static_assertions;

#[zerocopy_derive::inline_assert_size_eq(1)]
struct test_size_neq_struct {
    i: i8
}
