// DO NOT RUN THIS NATIVELY.
//
// The definition is `#[track_caller]`, so its ABI takes one implicit trailing argument, but the
// `extern "Rust"` declaration used for the call omits the attribute and the caller passes none.
// The Rust Reference classifies this as undefined behaviour. The harness runs this file only under
// an interpreter and records whether the interpreter reports the mismatch.
use std::panic::Location;

#[no_mangle]
#[track_caller]
#[inline(never)]
pub fn exported_tracked() -> u32 {
    Location::caller().line()
}

mod decl {
    extern "Rust" {
        // Missing `#[track_caller]`: an arity-`N` declaration for an arity-`N + 1` definition.
        pub fn exported_tracked() -> u32;
    }
}

fn main() {
    let line = unsafe { decl::exported_tracked() }; // @MISMATCH_CALL
    println!("MISMATCH_NOT_DETECTED={line}");
}
