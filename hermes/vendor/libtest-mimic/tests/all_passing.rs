use common::{args, check};
use libtest_mimic::{Completion, Conclusion, Trial};
use pretty_assertions::assert_eq;

use crate::common::do_run;

#[macro_use]
mod common;

fn tests() -> Vec<Trial> {
    vec![
        Trial::test("foo", || Ok(())),
        Trial::test("bar", || Ok(())),
        Trial::test("barro", || Ok(())),
        // Passed
        Trial::ignorable_test("baz", || Ok(Completion::Completed)),
        // Ignored with a reason
        Trial::ignorable_test("qux", || Ok(Completion::ignored_with("very valid reason"))),
        // Ignored with no reason
        Trial::ignorable_test("quux", || Ok(Completion::ignored())),
    ]
}

#[test]
fn normal() {
    check(
        args([]),
        tests,
        6,
        Conclusion {
            num_filtered_out: 0,
            num_passed: 4,
            num_failed: 0,
            num_ignored: 2,
            num_measured: 0,
        },
        "
            test foo   ... ok
            test bar   ... ok
            test barro ... ok
            test baz   ... ok
            test qux   ... ignored (very valid reason)
            test quux  ... ignored
        ",
    );
}

#[test]
fn filter_one() {
    check(
        args(["foo"]),
        tests,
        1,
        Conclusion {
            num_filtered_out: 5,
            num_passed: 1,
            num_failed: 0,
            num_ignored: 0,
            num_measured: 0,
        },
        "test foo ... ok",
    );
}

#[test]
fn filter_two() {
    check(
        args(["bar"]),
        tests,
        2,
        Conclusion {
            num_filtered_out: 4,
            num_passed: 2,
            num_failed: 0,
            num_ignored: 0,
            num_measured: 0,
        },
        "
            test bar   ... ok
            test barro ... ok
        ",
    );
}

#[test]
fn filter_exact() {
    check(
        args(["bar", "--exact"]),
        tests,
        1,
        Conclusion {
            num_filtered_out: 5,
            num_passed: 1,
            num_failed: 0,
            num_ignored: 0,
            num_measured: 0,
        },
        "test bar ... ok",
    );
}

#[test]
fn filter_two_and_skip() {
    check(
        args(["--skip", "barro", "bar"]),
        tests,
        1,
        Conclusion {
            num_filtered_out: 5,
            num_passed: 1,
            num_failed: 0,
            num_ignored: 0,
            num_measured: 0,
        },
        "test bar ... ok",
    );
}

#[test]
fn filter_runtime_ignored() {
    check(
        args(["qux", "--exact"]),
        tests,
        1,
        Conclusion {
            num_filtered_out: 5,
            num_passed: 0,
            num_failed: 0,
            num_ignored: 1,
            num_measured: 0,
        },
        "test qux ... ignored (very valid reason)",
    );
}

#[test]
fn skip_nothing() {
    check(
        args(["--skip", "peter"]),
        tests,
        6,
        Conclusion {
            num_filtered_out: 0,
            num_passed: 4,
            num_failed: 0,
            num_ignored: 2,
            num_measured: 0,
        },
        "
            test foo   ... ok
            test bar   ... ok
            test barro ... ok
            test baz   ... ok
            test qux   ... ignored (very valid reason)
            test quux  ... ignored
        ",
    );
}

#[test]
fn skip_two() {
    check(
        args(["--skip", "bar"]),
        tests,
        4,
        Conclusion {
            num_filtered_out: 2,
            num_passed: 2,
            num_failed: 0,
            num_ignored: 2,
            num_measured: 0,
        },
        "
            test foo  ... ok
            test baz  ... ok
            test qux  ... ignored (very valid reason)
            test quux ... ignored
        ",
    );
}

#[test]
fn skip_exact() {
    check(
        args(["--exact", "--skip", "bar"]),
        tests,
        5,
        Conclusion {
            num_filtered_out: 1,
            num_passed: 3,
            num_failed: 0,
            num_ignored: 2,
            num_measured: 0,
        },
        "
            test foo   ... ok
            test barro ... ok
            test baz   ... ok
            test qux   ... ignored (very valid reason)
            test quux  ... ignored
        ",
    );
}

#[test]
fn terse_output() {
    let (c, out) = do_run(args(["--format", "terse"]), tests());
    assert_eq!(
        c,
        Conclusion {
            num_filtered_out: 0,
            num_passed: 4,
            num_failed: 0,
            num_ignored: 2,
            num_measured: 0,
        }
    );
    assert_log!(
        out,
        "
        running 6 tests
        ....ii
        test result: ok. 4 passed; 0 failed; 2 ignored; 0 measured; 0 filtered out; \
            finished in 0.00s
    "
    );
}
