use std::time::Duration;
use libtest_mimic::{Trial, Arguments};


#[test]
fn check_test_on_main_thread() {
    let outer_thread = std::thread::current().id();

    let mut args = Arguments::default();
    args.test_threads = Some(1);
    let conclusion = libtest_mimic::run(&args, vec![Trial::test("check", move || {
        assert_eq!(outer_thread, std::thread::current().id());
        Ok(())
    })]);

    assert_eq!(conclusion.num_passed, 1);
}

#[test]
fn all_tests_run_on_single_thread() {
    let mut args = Arguments::default();
    args.test_threads = Some(1);
    let trials = vec![
        Trial::test("a", move || Ok(())),
        Trial::test("b", move || Ok(())),
        Trial::test("c", move || Ok(())),
    ];
    let conclusion = libtest_mimic::run(&args, trials);
    assert_eq!(conclusion.num_passed, 3);
}

#[test]
fn all_tests_run_on_two_threads() {
    let mut args = Arguments::default();
    args.test_threads = Some(2);
    let trials = vec![
        Trial::test("a", move || Ok(())),
        Trial::test("b", move || Ok(())),
        Trial::test("c", move || Ok(())),
        Trial::test("d", move || Ok(())),
        Trial::test("e", move || Ok(())),
    ];
    let conclusion = libtest_mimic::run(&args, trials);
    assert_eq!(conclusion.num_passed, 5);
}

// I know this is not a super clean test, but I think spurious failures should
// be veeeery limited. The value this test provides outweights the potential
// jankiness I think.
#[test]
fn multi_threads_are_used() {
    let mut args = Arguments::default();
    args.test_threads = Some(4);
    let trials = vec![
        Trial::test("a", move || { std::thread::sleep(Duration::from_secs(1)); Ok(()) }),
        Trial::test("b", move || { std::thread::sleep(Duration::from_secs(1)); Ok(()) }),
        Trial::test("c", move || { std::thread::sleep(Duration::from_secs(1)); Ok(()) }),
        Trial::test("d", move || { std::thread::sleep(Duration::from_secs(1)); Ok(()) }),
    ];
    let before = std::time::Instant::now();
    let _ = libtest_mimic::run(&args, trials);
    if before.elapsed() >= Duration::from_secs(2) {
        panic!("Seems like tests are not executed in parallel");
    }
}
