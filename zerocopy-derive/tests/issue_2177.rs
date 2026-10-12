// This test reproduces the issue reported in https://github.com/google/zerocopy/issues/2177
// It uses a macro to wrap the derive, which triggers the private_bounds lint unless suppressed.

#![allow(missing_docs)]
use zerocopy::KnownLayout;

macro_rules! define {
    ($name:ident, $repr:ty) => {
        #[derive(KnownLayout)]
        #[repr(C)]
        pub struct $name($repr);
    }
}

define!(Foo, u8);

#[test]
fn test_issue_2177() {
    let _ = Foo(0);
}
