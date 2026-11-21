// A `#[track_caller]` definition reached through an `extern "Rust"` declaration that repeats the
// attribute: declaration and definition agree on the ABI.
use std::panic::Location;

#[no_mangle]
#[track_caller]
#[inline(never)]
pub fn exported_tracked_ok() -> u32 {
    Location::caller().line()
}

mod decl {
    extern "Rust" {
        #[track_caller]
        pub fn exported_tracked_ok() -> u32;
    }
}

fn main() {
    let line = unsafe { decl::exported_tracked_ok() }; // @EXTERN_DECL_CALL
    println!("EXTERN_DECL_MATCH={line}");
}
