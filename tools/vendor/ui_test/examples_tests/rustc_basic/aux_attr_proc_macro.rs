//@aux-build:proc_macro_attr.rs
//@check-pass

extern crate proc_macro_attr;

#[proc_macro_attr::passthrough]
pub fn f() {}

pub fn g() {}
