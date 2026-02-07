//! Write your own tests and benchmarks that look and behave like built-in tests!
//!
//! This is a simple and small test harness that mimics the original `libtest`
//! (used by `cargo test`/`rustc --test`). That means: all output looks pretty
//! much like `cargo test` and most CLI arguments are understood and used. With
//! that plumbing work out of the way, your test runner can focus on the actual
//! testing.
//!
//! For a small real world example, see [`examples/tidy.rs`][1].
//!
//! [1]: https://github.com/LukasKalbertodt/libtest-mimic/blob/master/examples/tidy.rs
//!
//! # Usage
//!
//! To use this, you most likely want to add a manual `[[test]]` section to
//! `Cargo.toml` and set `harness = false`. For example:
//!
//! ```toml
//! [[test]]
//! name = "mytest"
//! path = "tests/mytest.rs"
//! harness = false
//! ```
//!
//! And in `tests/mytest.rs` you would call [`run`] in the `main` function:
//!
//! ```no_run
//! use libtest_mimic::{Arguments, Trial};
//!
//!
//! // Parse command line arguments
//! let args = Arguments::from_args();
//!
//! // Create a list of tests and/or benchmarks (in this case: two dummy tests).
//! let tests = vec![
//!     Trial::test("succeeding_test", move || Ok(())),
//!     Trial::test("failing_test", move || Err("Woops".into())),
//! ];
//!
//! // Run all tests and exit the application appropriatly.
//! libtest_mimic::run(&args, tests).exit();
//! ```
//!
//! Instead of returning `Ok` or `Err` directly, you want to actually perform
//! your tests, of course. See [`Trial::test`] for more information on how to
//! define a test. You can of course list all your tests manually. But in many
//! cases it is useful to generate one test per file in a directory, for
//! example.
//!
//! You can then run `cargo test --test mytest` to run it. To see the CLI
//! arguments supported by this crate, run `cargo test --test mytest -- -h`.
//!
//!
//! # Known limitations and differences to the official test harness
//!
//! `libtest-mimic` works on a best-effort basis: it tries to be as close to
//! `libtest` as possible, but there are differences for a variety of reasons.
//! For example, some rarely used features might not be implemented, some
//! features are extremely difficult to implement, and removing minor,
//! unimportant differences is just not worth the hassle.
//!
//! Some of the notable differences:
//!
//! - Output capture and `--nocapture`: simply not supported. The official
//!   `libtest` uses internal `std` functions to temporarily redirect output.
//!   `libtest-mimic` cannot use those. See [this issue][capture] for more
//!   information.
//! - `--format=junit`
//! - Also see [#13](https://github.com/LukasKalbertodt/libtest-mimic/issues/13)
//!
//! [capture]: https://github.com/LukasKalbertodt/libtest-mimic/issues/9

#![forbid(unsafe_code)]

use std::{
    borrow::Cow,
    fmt,
    process::{self, ExitCode},
    sync::{mpsc, Mutex},
    thread,
    time::Instant,
};

mod args;
mod printer;

use printer::Printer;

pub use crate::args::{Arguments, ColorSetting, FormatSetting};



/// A single test or benchmark.
///
/// The original `libtest` often calls benchmarks "tests", which is a bit
/// confusing. So in this library, it is called "trial".
///
/// A trial is created via [`Trial::test`] or [`Trial::bench`]. The trial's
/// `name` is printed and used for filtering. The `runner` is called when the
/// test/benchmark is executed to determine its outcome. If `runner` panics,
/// the trial is considered "failed". If you need the behavior of
/// `#[should_panic]` you need to catch the panic yourself. You likely want to
/// compare the panic payload to an expected value anyway.
pub struct Trial {
    runner: Box<dyn FnOnce(bool) -> Outcome + Send>,
    info: TestInfo,
}

impl Trial {
    /// Creates a (non-benchmark) test with the given name and runner.
    ///
    /// The runner returning `Ok(())` is interpreted as the test passing. If the
    /// runner returns `Err(_)`, the test is considered failed.
    pub fn test<R>(name: impl Into<String>, runner: R) -> Self
    where
        R: FnOnce() -> Result<(), Failed> + Send + 'static,
    {
        Self {
            runner: Box::new(move |_test_mode| match runner() {
                Ok(()) => Outcome::Passed,
                Err(failed) => Outcome::Failed(failed),
            }),
            info: TestInfo {
                name: name.into(),
                kind: String::new(),
                is_ignored: false,
                is_bench: false,
            },
        }
    }

    /// Creates a benchmark with the given name and runner.
    ///
    /// If the runner's parameter `test_mode` is `true`, the runner function
    /// should run all code just once, without measuring, just to make sure it
    /// does not panic. If the parameter is `false`, it should perform the
    /// actual benchmark. If `test_mode` is `true` you may return `Ok(None)`,
    /// but if it's `false`, you have to return a `Measurement`, or else the
    /// benchmark is considered a failure.
    ///
    /// `test_mode` is `true` if neither `--bench` nor `--test` are set, and
    /// `false` when `--bench` is set. If `--test` is set, benchmarks are not
    /// ran at all, and both flags cannot be set at the same time.
    pub fn bench<R>(name: impl Into<String>, runner: R) -> Self
    where
        R: FnOnce(bool) -> Result<Option<Measurement>, Failed> + Send + 'static,
    {
        Self {
            runner: Box::new(move |test_mode| match runner(test_mode) {
                Err(failed) => Outcome::Failed(failed),
                Ok(_) if test_mode => Outcome::Passed,
                Ok(Some(measurement)) => Outcome::Measured(measurement),
                Ok(None)
                    => Outcome::Failed("bench runner returned `Ok(None)` in bench mode".into()),
            }),
            info: TestInfo {
                name: name.into(),
                kind: String::new(),
                is_ignored: false,
                is_bench: true,
            },
        }
    }

    /// Sets the "kind" of this test/benchmark. If this string is not
    /// empty, it is printed in brackets before the test name (e.g.
    /// `test [my-kind] test_name`). (Default: *empty*)
    ///
    /// This is the only extension to the original libtest.
    pub fn with_kind(self, kind: impl Into<String>) -> Self {
        Self {
            info: TestInfo {
                kind: kind.into(),
                ..self.info
            },
            ..self
        }
    }

    /// Sets whether or not this test is considered "ignored". (Default: `false`)
    ///
    /// With the built-in test suite, you can annotate `#[ignore]` on tests to
    /// not execute them by default (for example because they take a long time
    /// or require a special environment). If the `--ignored` flag is set,
    /// ignored tests are executed, too.
    pub fn with_ignored_flag(self, is_ignored: bool) -> Self {
        Self {
            info: TestInfo {
                is_ignored,
                ..self.info
            },
            ..self
        }
    }

    /// Returns the name of this trial.
    pub fn name(&self) -> &str {
        &self.info.name
    }

    /// Returns the kind of this trial. If you have not set a kind, this is an
    /// empty string.
    pub fn kind(&self) -> &str {
        &self.info.kind
    }

    /// Returns whether this trial has been marked as *ignored*.
    pub fn has_ignored_flag(&self) -> bool {
        self.info.is_ignored
    }

    /// Returns `true` iff this trial is a test (as opposed to a benchmark).
    pub fn is_test(&self) -> bool {
        !self.info.is_bench
    }

    /// Returns `true` iff this trial is a benchmark (as opposed to a test).
    pub fn is_bench(&self) -> bool {
        self.info.is_bench
    }
}

impl fmt::Debug for Trial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        struct OpaqueRunner;
        impl fmt::Debug for OpaqueRunner {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str("<runner>")
            }
        }

        f.debug_struct("Test")
            .field("runner", &OpaqueRunner)
            .field("name", &self.info.name)
            .field("kind", &self.info.kind)
            .field("is_ignored", &self.info.is_ignored)
            .field("is_bench", &self.info.is_bench)
            .finish()
    }
}

#[derive(Debug)]
struct TestInfo {
    name: String,
    kind: String,
    is_ignored: bool,
    is_bench: bool,
}

impl TestInfo {
    fn test_name_with_kind(&self) -> Cow<'_, str> {
        if self.kind.is_empty() {
            Cow::Borrowed(&self.name)
        } else {
            Cow::Owned(format!("[{}] {}", self.kind, self.name))
        }
    }
}

/// Output of a benchmark.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Measurement {
    /// Average time in ns.
    pub avg: u64,

    /// Variance in ns.
    pub variance: u64,
}

/// Indicates that a test/benchmark has failed. Optionally carries a message.
///
/// You usually want to use the `From` impl of this type, which allows you to
/// convert any `T: fmt::Display` (e.g. `String`, `&str`, ...) into `Failed`.
#[derive(Debug, Clone)]
pub struct Failed {
    msg: Option<String>,
}

impl Failed {
    /// Creates an instance without message.
    pub fn without_message() -> Self {
        Self { msg: None }
    }

    /// Returns the message of this instance.
    pub fn message(&self) -> Option<&str> {
        self.msg.as_deref()
    }
}

impl<M: std::fmt::Display> From<M> for Failed {
    fn from(msg: M) -> Self {
        Self {
            msg: Some(msg.to_string())
        }
    }
}



/// The outcome of performing a test/benchmark.
#[derive(Debug, Clone)]
enum Outcome {
    /// The test passed.
    Passed,

    /// The test or benchmark failed.
    Failed(Failed),

    /// The test or benchmark was ignored.
    Ignored,

    /// The benchmark was successfully run.
    Measured(Measurement),
}

/// Contains information about the entire test run. Is returned by[`run`].
///
/// This type is marked as `#[must_use]`. Usually, you just call
/// [`exit()`][Conclusion::exit] on the result of `run` to exit the application
/// with the correct exit code. But you can also store this value and inspect
/// its data.
#[derive(Clone, Debug, PartialEq, Eq)]
#[must_use = "Call `exit()` or `exit_if_failed()` to set the correct return code"]
pub struct Conclusion {
    /// Number of tests and benchmarks that were filtered out (either by the
    /// filter-in pattern or by `--skip` arguments).
    pub num_filtered_out: u64,

    /// Number of passed tests.
    pub num_passed: u64,

    /// Number of failed tests and benchmarks.
    pub num_failed: u64,

    /// Number of ignored tests and benchmarks.
    pub num_ignored: u64,

    /// Number of benchmarks that successfully ran.
    pub num_measured: u64,
}

impl Conclusion {
    /// Returns an exit code that can be returned from `main` to signal
    /// success/failure to the calling process.
    pub fn exit_code(&self) -> ExitCode {
        if self.has_failed() {
            ExitCode::from(101)
        } else {
            ExitCode::SUCCESS
        }
    }

    /// Returns whether there have been any failures.
    pub fn has_failed(&self) -> bool {
        self.num_failed > 0
    }

    /// Exits the application with an appropriate error code (0 if all tests
    /// have passed, 101 if there have been failures). This uses
    /// [`process::exit`], meaning that destructors are not ran. Consider
    /// using [`Self::exit_code`] instead for a proper program cleanup.
    pub fn exit(&self) -> ! {
        self.exit_if_failed();
        process::exit(0);
    }

    /// Exits the application with error code 101 if there were any failures.
    /// Otherwise, returns normally. This uses [`process::exit`], meaning that
    /// destructors are not ran. Consider using [`Self::exit_code`] instead for
    /// a proper program cleanup.
    pub fn exit_if_failed(&self) {
        if self.has_failed() {
            process::exit(101)
        }
    }

    fn empty() -> Self {
        Self {
            num_filtered_out: 0,
            num_passed: 0,
            num_failed: 0,
            num_ignored: 0,
            num_measured: 0,
        }
    }
}

impl Arguments {
    /// Returns `true` if the given test should be ignored.
    fn is_ignored(&self, test: &Trial) -> bool {
        (test.info.is_ignored && !self.ignored && !self.include_ignored)
            || (test.info.is_bench && self.test)
            || (!test.info.is_bench && self.bench)
    }

    fn is_filtered_out(&self, test: &Trial) -> bool {
        let test_name = test.name();
        // Match against the full test name, including the kind. This upholds the invariant that if
        // --list prints out:
        //
        // <some string>: test
        //
        // then "--exact <some string>" runs exactly that test.
        let test_name_with_kind = test.info.test_name_with_kind();

        // If a filter was specified, apply this
        if let Some(filter) = &self.filter {
            match self.exact {
                // For exact matches, we want to match against either the test name (to maintain
                // backwards compatibility with older versions of libtest-mimic), or the test kind
                // (technically more correct with respect to matching against the output of --list.)
                true if test_name != filter && &test_name_with_kind != filter => return true,
                false if !test_name_with_kind.contains(filter) => return true,
                _ => {}
            };
        }

        // If any skip pattern were specified, test for all patterns.
        for skip_filter in &self.skip {
            match self.exact {
                // For exact matches, we want to match against either the test name (to maintain
                // backwards compatibility with older versions of libtest-mimic), or the test kind
                // (technically more correct with respect to matching against the output of --list.)
                true if test_name == skip_filter || &test_name_with_kind == skip_filter => {
                    return true
                }
                false if test_name_with_kind.contains(skip_filter) => return true,
                _ => {}
            }
        }

        if self.ignored && !test.info.is_ignored {
            return true;
        }

        false
    }
}

/// Runs all given trials (tests & benchmarks).
///
/// This is the central function of this crate. It provides the framework for
/// the testing harness. It does all the printing and house keeping.
///
/// The returned value contains a couple of useful information. See
/// [`Conclusion`] for more information. If `--list` was specified, a list is
/// printed and a dummy `Conclusion` is returned.
pub fn run(args: &Arguments, mut tests: Vec<Trial>) -> Conclusion {
    let start_instant = Instant::now();
    let mut conclusion = Conclusion::empty();

    // Apply filtering
    if args.filter.is_some() || !args.skip.is_empty() || args.ignored {
        let len_before = tests.len() as u64;
        tests.retain(|test| !args.is_filtered_out(test));
        conclusion.num_filtered_out = len_before - tests.len() as u64;
    }
    let tests = tests;

    // Create printer which is used for all output.
    let mut printer = printer::Printer::new(args, &tests);

    // If `--list` is specified, just print the list and return.
    if args.list {
        printer.print_list(&tests, args.ignored);
        return Conclusion::empty();
    }

    // Print number of tests
    printer.print_title(tests.len() as u64);

    let mut failed_tests = Vec::new();
    let mut handle_outcome = |outcome: Outcome, test: TestInfo, printer: &mut Printer| {
        printer.print_single_outcome(&test, &outcome);

        // Handle outcome
        match outcome {
            Outcome::Passed => conclusion.num_passed += 1,
            Outcome::Failed(failed) => {
                failed_tests.push((test, failed.msg));
                conclusion.num_failed += 1;
            },
            Outcome::Ignored => conclusion.num_ignored += 1,
            Outcome::Measured(_) => conclusion.num_measured += 1,
        }
    };

    // Execute all tests.
    let test_mode = !args.bench;

    let num_threads = platform_defaults_to_one_thread()
        .then_some(1)
        .or(args.test_threads)
        .or_else(|| std::thread::available_parallelism().ok().map(Into::into))
        .unwrap_or(1);

    if num_threads == 1 {
        // Run test sequentially in main thread
        for test in tests {
            // Print `test foo    ...`, run the test, then print the outcome in
            // the same line.
            printer.print_test(&test.info);
            let outcome = if args.is_ignored(&test) {
                Outcome::Ignored
            } else {
                run_single(test.runner, test_mode)
            };
            handle_outcome(outcome, test.info, &mut printer);
        }
    } else {
        // Run test in thread pool.
        let (sender, receiver) = mpsc::channel();

        let num_tests = tests.len();
        // TODO: this should use a mpmc channel, once that's stabilized in std.
        let iter = Mutex::new(tests.into_iter());
        thread::scope(|scope| {
            // Start worker threads
            for _ in 0..num_threads {
                scope.spawn(|| {
                    loop {
                        // Get next test to process from the iterator.
                        let Some(trial) = iter.lock().unwrap().next() else {
                            break;
                        };

                        let payload = if args.is_ignored(&trial) {
                            (Outcome::Ignored, trial.info)
                        } else {
                            let outcome = run_single(trial.runner, test_mode);
                            (outcome, trial.info)
                        };

                        // It's fine to ignore the result of sending. If the
                        // receiver has hung up, everything will wind down soon
                        // anyway.
                        let _ = sender.send(payload);
                    }
                });
            }

            // Print results of tests that already dinished
            for (outcome, test_info) in receiver.iter().take(num_tests) {
                // In multithreaded mode, we do only print the start of the line
                // after the test ran, as otherwise it would lead to terribly
                // interleaved output.
                printer.print_test(&test_info);
                handle_outcome(outcome, test_info, &mut printer);
            }
        });

    }

    // Print failures if there were any, and the final summary.
    if !failed_tests.is_empty() {
        printer.print_failures(&failed_tests);
    }

    printer.print_summary(&conclusion, start_instant.elapsed());

    conclusion
}

/// Returns whether the current host platform should use a single thread by
/// default rather than a thread pool by default. Some platforms, such as
/// WebAssembly, don't have native support for threading at this time.
fn platform_defaults_to_one_thread() -> bool {
    cfg!(target_family = "wasm")
}

/// Runs the given runner, catching any panics and treating them as a failed test.
fn run_single(runner: Box<dyn FnOnce(bool) -> Outcome + Send>, test_mode: bool) -> Outcome {
    use std::panic::{catch_unwind, AssertUnwindSafe};

    catch_unwind(AssertUnwindSafe(move || runner(test_mode))).unwrap_or_else(|e| {
        // The `panic` information is just an `Any` object representing the
        // value the panic was invoked with. For most panics (which use
        // `panic!` like `println!`), this is either `&str` or `String`.
        let payload = e.downcast_ref::<String>()
            .map(|s| s.as_str())
            .or(e.downcast_ref::<&str>().map(|s| *s));

        let msg = match payload {
            Some(payload) => format!("test panicked: {payload}"),
            None => format!("test panicked"),
        };
        Outcome::Failed(msg.into())
    })
}
