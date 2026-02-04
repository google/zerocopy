//! Default argument processing when `ui_test` is used
//! as a test driver.

use std::{borrow::Cow, num::NonZeroUsize};

use color_eyre::eyre::{bail, ensure, Result};

/// Plain arguments if `ui_test` is used as a binary.
#[derive(Debug, Default)]
pub struct Args {
    /// Filters that will be used to match on individual tests
    pub filters: Vec<String>,

    /// Whether to error on mismatches between `.stderr` files and actual
    /// output.
    pub check: bool,

    /// Whether to overwrite `.stderr` files on mismtach with the actual
    /// output.
    pub bless: bool,

    /// Only run the test matching the filters exactly.
    pub exact: bool,

    /// Whether to only run ignored tests.
    pub ignored: bool,

    /// List the tests that can be run.
    pub list: bool,

    /// Choose an output format
    pub format: Format,

    /// The number of threads to use
    pub threads: Option<NonZeroUsize>,

    /// Skip tests whose names contain any of these entries.
    pub skip: Vec<String>,
}

/// Possible choices for styling the output.
#[derive(Debug, Copy, Clone, Default)]
pub enum Format {
    /// Print one line per test
    #[default]
    Pretty,
    /// Remove test lines once the test finishes and show a progress bar.
    Terse,
}

impl Args {
    /// Parse the program arguments.
    /// This is meant to be used if `ui_test` is used as a `harness=false` test, called from `cargo test`.
    pub fn test() -> Result<Self> {
        Self::default().parse_args(std::env::args().skip(1))
    }

    /// Parse arguments into an existing `Args` struct.
    pub fn parse_args(mut self, mut iter: impl Iterator<Item = String>) -> Result<Self> {
        while let Some(arg) = iter.next() {
            if arg == "--" {
                continue;
            }
            if arg == "--quiet" {
                self.format = Format::Terse;
            } else if arg == "--check" {
                self.check = true;
            } else if arg == "--bless" {
                self.bless = true;
            } else if arg == "--list" {
                self.list = true;
            } else if arg == "--exact" {
                self.exact = true;
            } else if arg == "--ignored" {
                self.ignored = true;
            } else if arg == "--nocapture" {
                // We ignore this flag for now.
            } else if let Some(format) = parse_value("--format", &arg, &mut iter)? {
                self.format = match &*format {
                    "terse" => Format::Terse,
                    "pretty" => Format::Pretty,
                    _ => bail!("unsupported format `{format}`"),
                };
            } else if let Some(skip) = parse_value("--skip", &arg, &mut iter)? {
                self.skip.push(skip.into_owned());
            } else if arg == "--help" {
                bail!("available flags: --quiet, --check, --bless, --test-threads=n, --skip")
            } else if let Some(n) = parse_value("--test-threads", &arg, &mut iter)? {
                self.threads = Some(n.parse()?);
            } else if arg.starts_with("--") {
                bail!(
                    "unknown command line flag `{arg}`: {:?}",
                    iter.collect::<Vec<_>>()
                );
            } else {
                self.filters.push(arg);
            }
        }
        Ok(self)
    }
}

fn parse_value<'a>(
    name: &str,
    arg: &'a str,
    iter: &mut impl Iterator<Item = String>,
) -> Result<Option<Cow<'a, str>>> {
    let with_eq = match arg.strip_prefix(name) {
        Some(s) => s,
        None => return Ok(None),
    };
    if let Some(n) = with_eq.strip_prefix('=') {
        Ok(Some(n.into()))
    } else {
        ensure!(with_eq.is_empty(), "`{name}` can only be followed by `=`");

        if let Some(next) = iter.next() {
            Ok(Some(next.into()))
        } else {
            bail!("`name` must be followed by a value")
        }
    }
}
