#![allow(dead_code, path_statements, clippy::all)]
#[must_use]
fn g() -> i32 { 1 }
fn r() -> Result<(), ()> { Ok(()) }
#[must_use = "the guard releases the lock when dropped"]
struct Guard;
fn guard() -> Guard { Guard }
fn call<F: Fn() -> i32>(f: F) -> i32 { f() }
fn call_r<F: Fn() -> Result<(), ()>>(f: F) -> Result<(), ()> { f() }
macro_rules! m { () => { g() } }
trait T { #[must_use] fn t(&self) -> i32; }
impl T for () { fn t(&self) -> i32 { 1 } }

fn main() {
    g();                                // R1  #[must_use] fn, bare call
    let _ = g();                        // R2  `let _ =` discard
    r();                                // R3  Result (must_use type)
    let h = g; h();                     // R4  must_use fn through a local fn pointer
    call(g);                            // R5  generic wrapper returning i32
    call_r(r);                          // R6  generic wrapper returning Result
    (|| g())();                         // R7  closure returning a must_use fn's value
    m!();                               // R8  macro expanding to a must_use call
    ().t();                             // R9  #[must_use] trait method
    guard();                            // R10 #[must_use = "..."] type
    Some(r());                          // R11 Option<Result<..>>
    (r(), 1);                           // R12 tuple containing Result
    Box::new(r());                      // R13 Box<Result<..>>
    [r()];                              // R14 [Result<..>; 1]
    drop(r());                          // R15 explicit drop
    1 + 1;                              // R16 arithmetic operator
    vec![1].iter().map(|x| x + 1);      // R17 lazy iterator adaptor
    let v: Vec<i32> = Vec::new(); v.len(); // R18 Vec::len
}
