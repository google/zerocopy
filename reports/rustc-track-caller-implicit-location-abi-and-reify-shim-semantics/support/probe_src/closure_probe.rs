// `#[track_caller]` on closures is unstable (`closure_track_caller`); this file needs a nightly.
// Only the last two path components of each file name are printed, so the output does not depend
// on where the standard library sources live.
#![feature(closure_track_caller, stmt_expr_attributes)]
use std::hint::black_box;
use std::panic::Location;

fn tail(l: &Location<'_>) -> String {
    let parts: Vec<&str> = l.file().rsplit('/').take(2).collect();
    let name = parts.into_iter().rev().collect::<Vec<_>>().join("/");
    format!("{}:{}", name, l.line())
}

#[inline(never)]
fn call_fn_generic<F: Fn() -> String>(f: &F) -> String {
    f() // @CLOSURE_GENERIC_FN_SITE
}

#[inline(never)]
fn call_once_generic<F: FnOnce() -> String>(f: F) -> String {
    f() // @CLOSURE_GENERIC_ONCE_SITE
}

fn main() {
    let c = #[track_caller] || tail(Location::caller()); // @CLOSURE_DEF (never reported)
    let direct = c(); // @CLOSURE_DIRECT_SITE
    let dyn_ref: &dyn Fn() -> String = black_box(&c);
    let via_dyn = dyn_ref(); // @CLOSURE_DYN_SITE (never reported)
    let generic_fn = call_fn_generic(&c);
    let generic_once = call_once_generic(c);
    let boxed: Box<dyn FnOnce() -> String> = black_box(Box::new(c));
    let via_box_once = boxed(); // @CLOSURE_BOX_ONCE_SITE (never reported)
    println!("CLOSURE_DIRECT={direct}");
    println!("CLOSURE_DYN={via_dyn}");
    println!("CLOSURE_GENERIC_FN={generic_fn}");
    println!("CLOSURE_GENERIC_ONCE={generic_once}");
    println!("CLOSURE_BOX_ONCE={via_box_once}");
}
