// Copyright (c) The datatest-stable Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{data_source::TestEntry, DataSource, Result};
use camino::{Utf8Path, Utf8PathBuf};
use libtest_mimic::{Arguments, Trial};
use std::{path::Path, process::ExitCode};

#[doc(hidden)]
pub fn runner(requirements: &[Requirements]) -> ExitCode {
    if let Some(cwd) = custom_cwd() {
        std::env::set_current_dir(cwd).expect("set custom working directory");
    }

    let args = Arguments::from_args();

    let tests = find_tests(&args, requirements);

    let conclusion = libtest_mimic::run(&args, tests);

    // This used to use `Conclusion::exit`, but that exits the process via `std::process::exit` as
    // of libtest-mimic 0.7.0. This breaks some things, e.g. llvm-cov on Windows.
    // https://github.com/nextest-rs/datatest-stable/issues/20
    //
    // Use `std::process::ExitCode` instead, and return it in main.

    conclusion.exit_code()
}

/// One of our tests requires that a custom working directory be set. This function is used to do
/// that.
fn custom_cwd() -> Option<Utf8PathBuf> {
    std::env::var("__DATATEST_CWD").ok().map(Utf8PathBuf::from)
}

fn find_tests(args: &Arguments, requirements: &[Requirements]) -> Vec<Trial> {
    let tests: Vec<_> = if let Some(exact_filter) = exact_filter(args) {
        let exact_tests: Vec<_> = requirements
            .iter()
            .filter_map(|req| req.exact(exact_filter))
            .collect();

        match NextestKind::determine() {
            NextestKind::InUse { process_per_test } => {
                if exact_tests.is_empty() {
                    panic!("Failed to find exact match for filter {exact_filter}");
                }
                if process_per_test && exact_tests.len() > 1 {
                    panic!(
                        "Only expected one but found {} exact matches for filter {exact_filter}",
                        exact_tests.len()
                    );
                }
            }
            NextestKind::NotInUse => {}
        }

        exact_tests
    } else if is_full_scan_forbidden(args) {
        panic!("Exact filter was expected to be used");
    } else {
        let mut tests: Vec<_> = requirements.iter().flat_map(|req| req.expand()).collect();
        tests.sort_unstable_by(|a, b| a.name().cmp(b.name()));
        tests
    };
    tests
}

#[derive(Clone, Copy, Debug)]
enum NextestKind {
    NotInUse,
    InUse { process_per_test: bool },
}

impl NextestKind {
    fn determine() -> Self {
        if std::env::var("NEXTEST").as_deref() == Ok("1") {
            // Process-per-test means that exactly one test should be run.
            let process_per_test =
                std::env::var("NEXTEST_EXECUTION_MODE").as_deref() == Ok("process-per-test");
            Self::InUse { process_per_test }
        } else {
            Self::NotInUse
        }
    }
}

fn is_full_scan_forbidden(args: &Arguments) -> bool {
    !args.list && std::env::var("__DATATEST_FULL_SCAN_FORBIDDEN").as_deref() == Ok("1")
}

fn exact_filter(args: &Arguments) -> Option<&str> {
    if args.exact && args.skip.is_empty() {
        args.filter.as_deref()
    } else {
        None
    }
}

#[doc(hidden)]
pub struct Requirements {
    test: TestFn,
    test_name: String,
    root: DataSource,
    pattern: String,
}

impl Requirements {
    #[doc(hidden)]
    pub fn new(test: TestFn, test_name: String, root: DataSource, pattern: String) -> Self {
        // include_dir data sources aren't compatible with test functions that
        // don't accept the contents as an argument.
        if !test.loads_data() && root.is_in_memory() {
            panic!(
                "test data for '{}' is stored in memory, so it \
                must accept file contents as an argument",
                test_name
            );
        }

        Self {
            test,
            test_name,
            root,
            pattern,
        }
    }

    fn trial(&self, entry: TestEntry) -> Trial {
        let testfn = self.test;
        let name = entry.derive_test_name(&self.test_name);
        Trial::test(name, move || {
            testfn
                .call(entry)
                .map_err(|err| format!("{:?}", err).into())
        })
    }

    fn exact(&self, filter: &str) -> Option<Trial> {
        let entry = self.root.derive_exact(filter, &self.test_name)?;
        entry.exists().then(|| self.trial(entry))
    }

    /// Scans all files in a given directory, finds matching ones and generates a test descriptor
    /// for each of them.
    fn expand(&self) -> Vec<Trial> {
        let re = fancy_regex::Regex::new(&self.pattern)
            .unwrap_or_else(|_| panic!("invalid regular expression: '{}'", self.pattern));

        let tests: Vec<_> = self
            .root
            .walk_files()
            .filter_map(|entry_res| {
                let entry = entry_res.expect("error reading directory");
                let path_str = entry.match_path().as_str();
                if re.is_match(path_str).unwrap_or_else(|error| {
                    panic!(
                        "error matching pattern '{}' against path '{}' : {}",
                        self.pattern, path_str, error
                    )
                }) {
                    Some(self.trial(entry))
                } else {
                    None
                }
            })
            .collect();

        // We want to avoid silent fails due to typos in regexp!
        if tests.is_empty() {
            panic!(
                "no test cases found for test '{}' -- scanned {} with pattern '{}'",
                self.test_name,
                self.root.display(),
                self.pattern,
            );
        }

        tests
    }
}

// -- Polymorphic dispatch --

#[derive(Clone, Copy)]
#[doc(hidden)]
pub enum TestFn {
    // Functions that work on paths.
    Base(TestFnBase),
    /// Test functions that load a file as a string (UTF-8 text).
    LoadString(TestFnLoadString),
    /// Test functions that load a file as binary data.
    LoadBinary(TestFnLoadBinary),
}

impl TestFn {
    fn loads_data(&self) -> bool {
        match self {
            TestFn::Base(_) => false,
            TestFn::LoadString(_) | TestFn::LoadBinary(_) => true,
        }
    }

    fn call(&self, entry: TestEntry) -> Result<()> {
        match self {
            TestFn::Base(f) => {
                let path = entry
                    .disk_path()
                    .expect("test entry being on disk was checked in the constructor");
                f.call(path)
            }
            TestFn::LoadString(f) => f.call(entry),
            TestFn::LoadBinary(f) => f.call(entry),
        }
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub enum TestFnBase {
    Path(fn(&Path) -> Result<()>),
    Utf8Path(fn(&Utf8Path) -> Result<()>),
}

impl TestFnBase {
    fn call(&self, path: &Utf8Path) -> Result<()> {
        match self {
            TestFnBase::Path(f) => f(path.as_ref()),
            TestFnBase::Utf8Path(f) => f(path),
        }
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub enum TestFnLoadString {
    Path(fn(&Path, String) -> Result<()>),
    Utf8Path(fn(&Utf8Path, String) -> Result<()>),
}

impl TestFnLoadString {
    fn call(&self, entry: TestEntry) -> Result<()> {
        let contents = entry.read_as_string()?;
        match self {
            TestFnLoadString::Path(f) => f(entry.test_path().as_ref(), contents),
            TestFnLoadString::Utf8Path(f) => f(entry.test_path(), contents),
        }
    }
}

#[derive(Clone, Copy)]
#[doc(hidden)]
pub enum TestFnLoadBinary {
    Path(fn(&Path, Vec<u8>) -> Result<()>),
    Utf8Path(fn(&Utf8Path, Vec<u8>) -> Result<()>),
}

impl TestFnLoadBinary {
    fn call(&self, entry: TestEntry) -> Result<()> {
        let contents = entry.read()?;
        match self {
            TestFnLoadBinary::Path(f) => f(entry.test_path().as_ref(), contents),
            TestFnLoadBinary::Utf8Path(f) => f(entry.test_path(), contents),
        }
    }
}

/// Implementations to allow `TestFn` to be created with functions of one of several types.
///
/// datatest-stable supports several options for the shape of test functions. This code allows:
///
/// * the `harness!` macro to accept any of these types of functions, generating the same syntactic
///   code for each.
/// * for all of those functions to resolve to a single `TestFn` type which can do dynamic dispatch.
///
/// There are several challenges to overcome here, the main one being that you cannot have multiple
/// different kinds of `Fn`s impl the same trait. For example, rustc will not accept this code
/// ([playground](https://play.rust-lang.org/?version=stable&mode=debug&edition=2021&gist=007c814fb457bd4e95d0073745b5f8d9)):
///
/// ```rust,ignore
/// trait MyTrait {}
///
/// impl<F: Fn(u32)> MyTrait for F {}
/// impl<F: Fn(bool)> MyTrait for F {}
/// ```
///
/// This means that it is not possible to write code that is type-system generic over different
/// kinds of function types.
///
/// But since `harness!` is a macro, it can expand to code that's syntactically the same for each of
/// those function types, but semantically resolves to completely different types. That's exactly
/// what we do here.
///
/// This is a trick very similar to autoref specialization, though we don't use the automatic `&`
/// Rust inserts while dereferencing methods. See [autoref-specialization].
///
/// # Notes
///
/// We can't say `impl PathKind for fn(&Path) -> Result<()>` because Rust won't automatically coerce
/// the concrete function type to the function pointer. (If we could, then we wouldn't need to rely
/// on the macro-ness of `harness!` at all, and could just have a single trait implemented for all
/// the different function pointer types.) To address this, we use a two-step process.
///
/// * Step 1: Implement `PathKind` for all `F: Fn(&Path) -> Result<()>`. This allows a `.kind()`
///   method to exist which returns a new `PathTag` type.
/// * Step 2: Implement `PathTag::new` which only takes `fn(&Path) -> Result<()>`. *This* type can
///   coerce to the function pointer, which can be stored in the `TestFn` enum.
///
/// This two-step process is similar to the one documented in [autoref-specialization].
///
/// [autoref-specialization]: https://github.com/dtolnay/case-studies/blob/master/autoref-specialization/README.md
#[doc(hidden)]
pub mod test_kinds {

    use super::*;

    mod private {
        // We need to define a separate Sealed for each of the tags below, because Rust doesn't allow
        // multiple kinds of F: Fn(T) -> Result<()> to implement the same trait.
        pub trait PathSealed {}
        pub trait Utf8PathSealed {}
        pub trait PathStringSealed {}
        pub trait Utf8PathStringSealed {}
        pub trait PathBytesSealed {}
        pub trait Utf8PathBytesSealed {}
    }

    // -- Paths --

    #[doc(hidden)]
    pub struct PathTag;

    impl PathTag {
        #[inline]
        pub fn resolve(self, f: fn(&Path) -> Result<()>) -> TestFn {
            TestFn::Base(TestFnBase::Path(f))
        }
    }

    #[doc(hidden)]
    pub trait PathKind: private::PathSealed {
        #[inline]
        fn kind(&self) -> PathTag {
            PathTag
        }
    }

    impl<F: Fn(&Path) -> Result<()>> private::PathSealed for F {}
    impl<F: Fn(&Path) -> Result<()>> PathKind for F {}

    // -- UTF-8 paths --

    #[doc(hidden)]
    pub struct Utf8PathTag;

    impl Utf8PathTag {
        #[inline]
        pub fn resolve(&self, f: fn(&Utf8Path) -> Result<()>) -> TestFn {
            TestFn::Base(TestFnBase::Utf8Path(f))
        }
    }

    #[doc(hidden)]
    pub trait Utf8PathKind: private::Utf8PathSealed {
        #[inline]
        fn kind(&self) -> Utf8PathTag {
            Utf8PathTag
        }
    }

    impl<F: Fn(&Utf8Path) -> Result<()>> private::Utf8PathSealed for F {}
    impl<F: Fn(&Utf8Path) -> Result<()>> Utf8PathKind for F {}

    // -- Path, load file as string --

    #[doc(hidden)]
    pub struct PathStringTag;

    impl PathStringTag {
        #[inline]
        pub fn resolve(self, f: fn(&Path, String) -> Result<()>) -> TestFn {
            TestFn::LoadString(TestFnLoadString::Path(f))
        }
    }

    #[doc(hidden)]
    pub trait PathStringKind: private::PathStringSealed {
        #[inline]
        fn kind(&self) -> PathStringTag {
            PathStringTag
        }
    }

    impl<F: Fn(&Path, String) -> Result<()>> private::PathStringSealed for F {}
    impl<F: Fn(&Path, String) -> Result<()>> PathStringKind for F {}

    // -- Utf8Path, load file as string --

    #[doc(hidden)]
    pub struct Utf8PathStringTag;

    impl Utf8PathStringTag {
        #[inline]
        pub fn resolve(self, f: fn(&Utf8Path, String) -> Result<()>) -> TestFn {
            TestFn::LoadString(TestFnLoadString::Utf8Path(f))
        }
    }

    #[doc(hidden)]
    pub trait Utf8PathStringKind: private::Utf8PathStringSealed {
        #[inline]
        fn kind(&self) -> Utf8PathStringTag {
            Utf8PathStringTag
        }
    }

    impl<F: Fn(&Utf8Path, String) -> Result<()>> private::Utf8PathStringSealed for F {}
    impl<F: Fn(&Utf8Path, String) -> Result<()>> Utf8PathStringKind for F {}

    // -- Path, load file as binary --

    #[doc(hidden)]
    pub struct PathBytesTag;

    impl PathBytesTag {
        #[inline]
        pub fn resolve(self, f: fn(&Path, Vec<u8>) -> Result<()>) -> TestFn {
            TestFn::LoadBinary(TestFnLoadBinary::Path(f))
        }
    }

    #[doc(hidden)]
    pub trait PathBytesKind: private::PathBytesSealed {
        #[inline]
        fn kind(&self) -> PathBytesTag {
            PathBytesTag
        }
    }

    impl<F: Fn(&Path, Vec<u8>) -> Result<()>> private::PathBytesSealed for F {}
    impl<F: Fn(&Path, Vec<u8>) -> Result<()>> PathBytesKind for F {}

    // -- Utf8Path, load file as binary --

    #[doc(hidden)]
    pub struct Utf8PathBytesTag;

    impl Utf8PathBytesTag {
        #[inline]
        pub fn resolve(self, f: fn(&Utf8Path, Vec<u8>) -> Result<()>) -> TestFn {
            TestFn::LoadBinary(TestFnLoadBinary::Utf8Path(f))
        }
    }

    #[doc(hidden)]
    pub trait Utf8PathBytesKind: private::Utf8PathBytesSealed {
        #[inline]
        fn kind(&self) -> Utf8PathBytesTag {
            Utf8PathBytesTag
        }
    }

    impl<F: Fn(&Utf8Path, Vec<u8>) -> Result<()>> private::Utf8PathBytesSealed for F {}
    impl<F: Fn(&Utf8Path, Vec<u8>) -> Result<()>> Utf8PathBytesKind for F {}
}

#[cfg(all(test, feature = "include-dir"))]
mod include_dir_tests {
    use super::*;
    use std::borrow::Cow;

    #[test]
    #[should_panic = "test data for 'my_test' is stored in memory, \
                      so it must accept file contents as an argument"]
    fn include_dir_without_arg() {
        fn my_test(_: &Path) -> Result<()> {
            Ok(())
        }

        Requirements::new(
            TestFn::Base(TestFnBase::Path(my_test)),
            "my_test".to_owned(),
            DataSource::IncludeDir(Cow::Owned(include_dir::include_dir!("tests/files"))),
            "xxx".to_owned(),
        );
    }
}
