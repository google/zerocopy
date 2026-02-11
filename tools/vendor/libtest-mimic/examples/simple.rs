extern crate libtest_mimic;

use std::{process::ExitCode, thread, time};
use libtest_mimic::{Arguments, Trial, Failed};


fn main() -> ExitCode {
    let args = Arguments::from_args();

    let tests = vec![
        Trial::test("check_toph", check_toph),
        Trial::test("check_sokka", check_sokka),
        Trial::test("long_computation", long_computation).with_ignored_flag(true),
        Trial::test("foo", compile_fail_dummy).with_kind("compile-fail"),
        Trial::test("check_katara", check_katara),
    ];

    libtest_mimic::run(&args, tests).exit_code()
}


// Tests

fn check_toph() -> Result<(), Failed> {
    Ok(())
}
fn check_katara() -> Result<(), Failed> {
    Ok(())
}
fn check_sokka() -> Result<(), Failed> {
    Err("Sokka tripped and fell :(".into())
}
fn long_computation() -> Result<(), Failed> {
    thread::sleep(time::Duration::from_secs(1));
    Ok(())
}
fn compile_fail_dummy() -> Result<(), Failed> {
    Ok(())
}
