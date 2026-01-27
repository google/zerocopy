// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    Error, Platform,
    errors::{RustcVersionVerboseParseError, TripleParseError},
};
use cfg_expr::{
    TargetPredicate,
    expr::TargetMatcher,
    target_lexicon,
    targets::{TargetInfo, get_builtin_target_by_triple},
};
use std::{borrow::Cow, cmp::Ordering, hash, str::FromStr};

/// A single, specific target, uniquely identified by a triple.
///
/// A `Triple` may be constructed through `new` or the `FromStr` implementation.
///
/// Every [`Platform`](crate::Platform) is backed by one of these.
///
/// # Standard and custom platforms
///
/// `target-spec` recognizes two kinds of platforms:
///
/// * **Standard platforms:** These platforms are only specified by their triple string, either
///   directly or via a [`Triple`]. For example, the platform `x86_64-unknown-linux-gnu` is a
///   standard platform since it is recognized by Rust.
///
///   All [builtin platforms](https://doc.rust-lang.org/nightly/rustc/platform-support.html) are
///   standard platforms.
///
///   By default, if a platform isn't builtin, target-spec attempts to heuristically determine the
///   characteristics of the platform based on the triple string. (Use the
///   [`new_strict`](Self::new_strict) constructor to disable this.)
///
/// * **Custom platforms:** These platforms are specified via both a triple string and a JSON file
///   in the format [defined by
///   Rust](https://docs.rust-embedded.org/embedonomicon/custom-target.html). Custom platforms are
///   used for targets not recognized by Rust.
///
/// # Examples
///
/// ```
/// use target_spec::Triple;
///
/// // Parse a simple target.
/// let target = Triple::new("x86_64-unknown-linux-gnu").unwrap();
/// // This is not a valid triple.
/// let err = Triple::new("cannot-be-known").unwrap_err();
/// ```
#[derive(Clone, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub struct Triple {
    inner: TripleInner,
}

impl Triple {
    /// Creates a new `Triple` from a triple string.
    pub fn new(triple_str: impl Into<Cow<'static, str>>) -> Result<Self, TripleParseError> {
        let inner = TripleInner::new(triple_str.into())?;
        Ok(Self { inner })
    }

    /// Creates a new `Triple` from a triple string.
    ///
    /// This constructor only consults the builtin platform table, and does not attempt to
    /// heuristically determine the platform's characteristics based on the triple string.
    pub fn new_strict(triple_str: impl Into<Cow<'static, str>>) -> Result<Self, TripleParseError> {
        let inner = TripleInner::new_strict(triple_str.into())?;
        Ok(Self { inner })
    }

    /// Creates a new standard `Triple` from `rustc -vV` output.
    ///
    /// # Example
    ///
    /// ```
    /// // This is the typical output of `rustc -vV`.
    /// let output = b"rustc 1.84.1 (e71f9a9a9 2025-01-27)
    /// binary: rustc
    /// commit-hash: e71f9a9a98b0faf423844bf0ba7438f29dc27d58
    /// commit-date: 2025-01-27
    /// host: x86_64-unknown-linux-gnu
    /// release: 1.84.1
    /// LLVM version: 19.1.5";
    ///
    /// let triple = target_spec::Triple::from_rustc_version_verbose(output).unwrap();
    /// assert_eq!(triple.as_str(), "x86_64-unknown-linux-gnu");
    /// ```
    pub fn from_rustc_version_verbose(output: impl AsRef<[u8]>) -> Result<Self, Error> {
        let output_slice = output.as_ref();
        let output = std::str::from_utf8(output_slice).map_err(|_| {
            // Get a better error message in this case via
            // std::string::FromUtf8Error.
            let output_vec = output_slice.to_vec();
            Error::RustcVersionVerboseParse(RustcVersionVerboseParseError::InvalidUtf8(
                String::from_utf8(output_vec)
                    .expect_err("we just failed to convert to UTF-8 above"),
            ))
        })?;

        // Look for the line beginning with `host: ` and extract the triple.
        // (This is a bit fragile, but it's what Cargo does.)
        let triple_str = output
            .lines()
            .find_map(|line| line.strip_prefix("host: "))
            .ok_or_else(|| {
                Error::RustcVersionVerboseParse(RustcVersionVerboseParseError::MissingHostLine {
                    output: output.to_owned(),
                })
            })?;

        // Now look up the triple.
        Self::new(triple_str.to_owned()).map_err(Error::UnknownPlatformTriple)
    }

    /// Creates a new custom `Triple` from the given triple string and JSON specification.
    #[cfg(feature = "custom")]
    pub fn new_custom(
        triple_str: impl Into<Cow<'static, str>>,
        json: &str,
    ) -> Result<Self, crate::errors::CustomTripleCreateError> {
        use crate::custom::TargetDefinition;

        let triple_str = triple_str.into();
        let target_def: TargetDefinition = serde_json::from_str(json).map_err(|error| {
            crate::errors::CustomTripleCreateError::DeserializeJson {
                triple: triple_str.to_string(),
                input: json.to_string(),
                error: error.into(),
            }
        })?;
        #[cfg(feature = "summaries")]
        let minified_json =
            serde_json::to_string(&target_def).expect("serialization is infallible");

        let target_info = Box::new(target_def.into_target_info(triple_str));
        Ok(Self {
            inner: TripleInner::Custom {
                target_info,
                #[cfg(feature = "summaries")]
                json: minified_json,
            },
        })
    }

    /// Returns the string corresponding to this triple.
    #[inline]
    pub fn as_str(&self) -> &str {
        self.inner.as_str()
    }

    /// Returns true if this is a triple corresponding to a standard platform.
    ///
    /// A standard platform can be either builtin, or heuristically determined.
    ///
    /// # Examples
    ///
    /// ```
    /// use target_spec::Triple;
    ///
    /// // x86_64-unknown-linux-gnu is Linux x86_64.
    /// let platform = Triple::new("x86_64-unknown-linux-gnu").unwrap();
    /// assert!(platform.is_standard());
    /// ```
    pub fn is_standard(&self) -> bool {
        self.inner.is_standard()
    }

    /// Returns true if this is a triple corresponding to a builtin platform.
    ///
    /// # Examples
    ///
    /// ```
    /// use target_spec::Triple;
    ///
    /// // x86_64-unknown-linux-gnu is Linux x86_64, which is a Rust tier 1 platform.
    /// let triple = Triple::new("x86_64-unknown-linux-gnu").unwrap();
    /// assert!(triple.is_builtin());
    /// ```
    #[inline]
    pub fn is_builtin(&self) -> bool {
        self.inner.is_builtin()
    }

    /// Returns true if this triple was heuristically determined.
    ///
    /// All heuristically determined platforms are standard, but most of the time, standard
    /// platforms are builtin.
    ///
    /// # Examples
    ///
    /// ```
    /// use target_spec::Triple;
    ///
    /// // armv5te-apple-darwin is not a real platform, but target-spec can heuristically
    /// // guess at its characteristics.
    /// let triple = Triple::new("armv5te-apple-darwin").unwrap();
    /// assert!(triple.is_heuristic());
    /// ```
    pub fn is_heuristic(&self) -> bool {
        self.inner.is_heuristic()
    }

    /// Returns true if this is a custom platform.
    ///
    /// This is always available, but if the `custom` feature isn't turned on this always returns
    /// false.
    pub fn is_custom(&self) -> bool {
        self.inner.is_custom()
    }

    /// Evaluates this triple against the given platform.
    ///
    /// This simply compares `self`'s string representation against the `Triple` the platform is
    /// based on, ignoring target features and flags.
    #[inline]
    pub fn eval(&self, platform: &Platform) -> bool {
        self.as_str() == platform.triple_str()
    }

    // Use cfg-expr's target matcher.
    #[inline]
    pub(crate) fn matches(&self, tp: &TargetPredicate) -> bool {
        self.inner.matches(tp)
    }

    #[cfg(feature = "summaries")]
    pub(crate) fn custom_json(&self) -> Option<&str> {
        self.inner.custom_json()
    }
}

impl FromStr for Triple {
    type Err = TripleParseError;

    fn from_str(triple_str: &str) -> Result<Self, Self::Err> {
        let inner = TripleInner::from_borrowed_str(triple_str)?;
        Ok(Self { inner })
    }
}

/// Inner representation of a triple.
#[derive(Clone, Debug)]
enum TripleInner {
    /// Prefer the builtin representation as it's more accurate.
    Builtin(&'static TargetInfo),

    /// A custom triple.
    #[cfg(feature = "custom")]
    Custom {
        target_info: Box<cfg_expr::targets::TargetInfo>,
        // The JSON is only needed if summaries are enabled.
        #[cfg(feature = "summaries")]
        json: String,
    },

    /// Fall back to the lexicon representation.
    Lexicon {
        triple_str: Cow<'static, str>,
        lexicon_triple: target_lexicon::Triple,
    },
}

impl TripleInner {
    fn new(triple_str: Cow<'static, str>) -> Result<Self, TripleParseError> {
        // First try getting the builtin.
        if let Some(target_info) = get_builtin_target_by_triple(&triple_str) {
            return Ok(TripleInner::Builtin(target_info));
        }

        // Next, try getting the lexicon representation.
        match triple_str.parse::<target_lexicon::Triple>() {
            Ok(lexicon_triple) => Ok(TripleInner::Lexicon {
                triple_str,
                lexicon_triple,
            }),
            Err(lexicon_err) => Err(TripleParseError::new(triple_str, lexicon_err)),
        }
    }

    fn new_strict(triple_str: Cow<'static, str>) -> Result<Self, TripleParseError> {
        if let Some(target_info) = get_builtin_target_by_triple(&triple_str) {
            return Ok(TripleInner::Builtin(target_info));
        }
        Err(TripleParseError::new_strict(triple_str))
    }

    fn from_borrowed_str(triple_str: &str) -> Result<Self, TripleParseError> {
        // First try getting the builtin.
        if let Some(target_info) = get_builtin_target_by_triple(triple_str) {
            return Ok(TripleInner::Builtin(target_info));
        }

        // Next, try getting the lexicon representation.
        match triple_str.parse::<target_lexicon::Triple>() {
            Ok(lexicon_triple) => Ok(TripleInner::Lexicon {
                triple_str: triple_str.to_owned().into(),
                lexicon_triple,
            }),
            Err(lexicon_err) => Err(TripleParseError::new(
                triple_str.to_owned().into(),
                lexicon_err,
            )),
        }
    }

    fn is_standard(&self) -> bool {
        match self {
            TripleInner::Builtin(_) | TripleInner::Lexicon { .. } => true,
            #[cfg(feature = "custom")]
            TripleInner::Custom { .. } => false,
        }
    }

    fn is_builtin(&self) -> bool {
        match self {
            TripleInner::Builtin(_) => true,
            TripleInner::Lexicon { .. } => false,
            #[cfg(feature = "custom")]
            TripleInner::Custom { .. } => false,
        }
    }

    fn is_heuristic(&self) -> bool {
        match self {
            TripleInner::Builtin(_) => false,
            TripleInner::Lexicon { .. } => true,
            #[cfg(feature = "custom")]
            TripleInner::Custom { .. } => false,
        }
    }

    fn is_custom(&self) -> bool {
        match self {
            TripleInner::Builtin(_) | TripleInner::Lexicon { .. } => false,
            #[cfg(feature = "custom")]
            TripleInner::Custom { .. } => true,
        }
    }

    fn as_str(&self) -> &str {
        match self {
            TripleInner::Builtin(target_info) => target_info.triple.as_str(),
            #[cfg(feature = "custom")]
            TripleInner::Custom { target_info, .. } => target_info.triple.as_str(),
            TripleInner::Lexicon { triple_str, .. } => triple_str,
        }
    }

    fn matches(&self, tp: &TargetPredicate) -> bool {
        match self {
            TripleInner::Builtin(target_info) => target_info.matches(tp),
            #[cfg(feature = "custom")]
            TripleInner::Custom { target_info, .. } => target_info.matches(tp),
            TripleInner::Lexicon { lexicon_triple, .. } => lexicon_triple.matches(tp),
        }
    }

    #[cfg(feature = "summaries")]
    pub(crate) fn custom_json(&self) -> Option<&str> {
        match self {
            TripleInner::Builtin(_) => None,
            #[cfg(feature = "custom")]
            TripleInner::Custom { json, .. } => Some(json),
            TripleInner::Lexicon { .. } => None,
        }
    }

    fn project(&self) -> TripleInnerProjected<'_> {
        match self {
            TripleInner::Builtin(target_info) => {
                TripleInnerProjected::Builtin(target_info.triple.as_str())
            }
            #[cfg(feature = "custom")]
            TripleInner::Custom { target_info, .. } => TripleInnerProjected::Custom(target_info),
            TripleInner::Lexicon { triple_str, .. } => TripleInnerProjected::Lexicon(triple_str),
        }
    }
}

/// This implementation is used for trait impls.
#[derive(Eq, PartialEq, PartialOrd, Ord, Hash)]
enum TripleInnerProjected<'a> {
    // Don't need anything else for builtin and lexicon since it's a pure function of the input.
    Builtin(&'a str),
    #[cfg(feature = "custom")]
    Custom(&'a TargetInfo),
    Lexicon(&'a str),
}

impl PartialEq for TripleInner {
    fn eq(&self, other: &Self) -> bool {
        self.project().eq(&other.project())
    }
}

impl Eq for TripleInner {}

impl PartialOrd for TripleInner {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TripleInner {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.project().cmp(&other.project())
    }
}

impl hash::Hash for TripleInner {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        hash::Hash::hash(&self.project(), state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use target_lexicon::*;

    #[test]
    fn test_parse() {
        let target =
            super::Triple::new("x86_64-pc-darwin").expect("this triple is known to target-lexicon");

        let expected_triple = target_lexicon::Triple {
            architecture: Architecture::X86_64,
            vendor: Vendor::Pc,
            operating_system: OperatingSystem::Darwin(None),
            environment: Environment::Unknown,
            binary_format: BinaryFormat::Macho,
        };

        let actual_triple = match target.inner {
            TripleInner::Lexicon { lexicon_triple, .. } => lexicon_triple,
            TripleInner::Builtin(_) => {
                panic!("should not have been able to parse x86_64-pc-darwin as a builtin");
            }
            #[cfg(feature = "custom")]
            TripleInner::Custom { .. } => {
                panic!("not a custom platform")
            }
        };
        assert_eq!(
            actual_triple, expected_triple,
            "lexicon triple matched correctly"
        );
    }

    #[test]
    fn test_parse_rustc_version_verbose() {
        let rustc = std::env::var("RUSTC").unwrap_or_else(|_| "rustc".to_string());
        let output = std::process::Command::new(rustc)
            .arg("-vV")
            .output()
            .expect("rustc -vV is successful");
        if !output.status.success() {
            panic!("rustc -vV failed: {output:?}");
        }

        let triple = super::Triple::from_rustc_version_verbose(output.stdout).unwrap();
        assert!(triple.is_standard());
    }
}
