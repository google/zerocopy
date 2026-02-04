//! Datastructures and operations used for normalizing test output.

use bstr::ByteSlice;
use lazy_static::lazy_static;
use regex::bytes::{Captures, Regex};
use std::borrow::Cow;
use std::path::Path;

use crate::display;

/// A filter's match rule.
#[derive(Clone, Debug)]
pub enum Match {
    /// If the regex matches, the filter applies
    Regex(Regex),
    /// If the exact byte sequence is found, the filter applies
    Exact(Vec<u8>),
    /// Uses a heuristic to find backslashes in windows style paths
    PathBackslash,
}

impl Match {
    pub(crate) fn replace_all<'a>(&self, text: &'a [u8], replacement: &[u8]) -> Cow<'a, [u8]> {
        match self {
            Match::Regex(regex) => regex.replace_all(text, replacement),
            Match::Exact(needle) => text.replace(needle, replacement).into(),
            Match::PathBackslash => {
                lazy_static! {
                    static ref PATH_RE: Regex = Regex::new(
                        r"(?x)
                        (?:
                            # Match paths to files with extensions that don't include spaces
                            \\(?:[\pL\pN.\-_']+[/\\])*[\pL\pN.\-_']+\.\pL+
                        |
                            # Allow spaces in absolute paths
                            [A-Z]:\\(?:[\pL\pN.\-_'\ ]+[/\\])+
                        )",
                    )
                    .unwrap();
                }

                PATH_RE.replace_all(text, |caps: &Captures<'_>| {
                    caps[0].replace(r"\", replacement)
                })
            }
        }
    }
}

impl From<&'_ Path> for Match {
    fn from(v: &Path) -> Self {
        let mut v = display(v);
        // Normalize away windows canonicalized paths.
        if v.starts_with(r"//?/") {
            v.drain(0..4);
        }
        Self::Exact(v.into_bytes())
    }
}

impl From<Regex> for Match {
    fn from(v: Regex) -> Self {
        Self::Regex(v)
    }
}
