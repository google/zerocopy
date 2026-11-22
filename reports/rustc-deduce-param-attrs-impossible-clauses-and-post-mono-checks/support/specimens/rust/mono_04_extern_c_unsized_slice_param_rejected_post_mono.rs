#![feature(unsized_fn_params)]
pub extern "C" fn c_abi_unsized_slice(_s: [u8]) {}
