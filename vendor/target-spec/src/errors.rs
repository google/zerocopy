// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Errors returned by `target-spec`.

use std::{borrow::Cow, error, fmt, string::FromUtf8Error};

/// An error that happened during `target-spec` parsing or evaluation.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Error {
    /// A `cfg()` expression was invalid and could not be parsed.
    InvalidExpression(ExpressionParseError),
    /// The provided plain string (in the position that a `cfg()` expression would be) was unknown.
    InvalidTargetSpecString(PlainStringParseError),
    /// The provided platform triple was unknown.
    UnknownPlatformTriple(TripleParseError),
    /// Deprecated: this variant is no longer used.
    #[deprecated(
        since = "3.3.0",
        note = "this variant is no longer returned: instead, use CustomPlatformCreate"
    )]
    #[doc(hidden)]
    CustomTripleCreate(CustomTripleCreateError),
    /// An error occurred while creating a custom platform.
    CustomPlatformCreate(CustomTripleCreateError),
    /// An error occurred while parsing `rustc -vV` output.
    RustcVersionVerboseParse(RustcVersionVerboseParseError),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidExpression(_) => write!(f, "invalid cfg() expression"),
            Error::InvalidTargetSpecString(_) => {
                write!(f, "failed to parse target spec as a plain string")
            }
            Error::UnknownPlatformTriple(_) => {
                write!(f, "unknown platform triple")
            }
            #[allow(deprecated)]
            Error::CustomTripleCreate(_) => write!(f, "error creating custom triple"),
            Error::CustomPlatformCreate(_) => {
                write!(f, "error creating custom platform")
            }
            Error::RustcVersionVerboseParse(_) => {
                write!(f, "error parsing `rustc -vV` output")
            }
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Error::InvalidExpression(err) => Some(err),
            Error::InvalidTargetSpecString(err) => Some(err),
            Error::UnknownPlatformTriple(err) => Some(err),
            #[allow(deprecated)]
            Error::CustomTripleCreate(err) => Some(err),
            Error::CustomPlatformCreate(err) => Some(err),
            Error::RustcVersionVerboseParse(err) => Some(err),
        }
    }
}

// Note: ExpressionParseError is a duplicate of cfg_expr::error::ParseError, and is copied here
// because we don't want to expose that in a stable (1.0+) API.

/// An error returned in case a `TargetExpression` cannot be parsed.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct ExpressionParseError {
    /// The string we tried to parse.
    pub input: String,

    /// The range of characters in the original string that resulted
    /// in this error.
    pub span: std::ops::Range<usize>,

    /// The kind of error that occurred.
    pub kind: ExpressionParseErrorKind,
}

impl ExpressionParseError {
    pub(crate) fn new(input: &str, error: cfg_expr::ParseError) -> Self {
        // The error returned by cfg_expr::ParseError does not include the leading 'cfg('. Use the
        // original input and add 4 which is the length of 'cfg('.
        let span = if input.starts_with("cfg(") && input.ends_with(')') {
            (error.span.start + 4)..(error.span.end + 4)
        } else {
            error.span
        };
        Self {
            input: input.to_owned(),
            span,
            kind: ExpressionParseErrorKind::from_cfg_expr(error.reason),
        }
    }
}

impl fmt::Display for ExpressionParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "error parsing cfg() expression")
    }
}

impl error::Error for ExpressionParseError {}

/// The kind of [`ExpressionParseError`] that occurred.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum ExpressionParseErrorKind {
    /// not() takes exactly 1 predicate, unlike all() and any()
    InvalidNot(usize),
    /// The characters are not valid in an cfg expression
    InvalidCharacters,
    /// An opening parens was unmatched with a closing parens
    UnclosedParens,
    /// A closing parens was unmatched with an opening parens
    UnopenedParens,
    /// An opening quotes was unmatched with a closing quotes
    UnclosedQuotes,
    /// A closing quotes was unmatched with an opening quotes
    UnopenedQuotes,
    /// The expression does not contain any valid terms
    Empty,
    /// Found an unexpected term, which wasn't one of the expected terms that
    /// is listed
    Unexpected {
        /// The list of expected terms.
        expected: &'static [&'static str],
    },
    /// Failed to parse an integer value
    InvalidInteger,
    /// The root cfg() may only contain a single predicate
    MultipleRootPredicates,
    /// A `target_has_atomic` predicate didn't correctly parse.
    InvalidHasAtomic,
    /// An element was not part of the builtin information in rustc
    UnknownBuiltin,
}

impl ExpressionParseErrorKind {
    fn from_cfg_expr(reason: cfg_expr::error::Reason) -> Self {
        use cfg_expr::error::Reason::*;

        match reason {
            InvalidCharacters => Self::InvalidCharacters,
            UnclosedParens => Self::UnclosedParens,
            UnopenedParens => Self::UnopenedParens,
            UnclosedQuotes => Self::UnclosedQuotes,
            UnopenedQuotes => Self::UnopenedQuotes,
            Empty => Self::Empty,
            Unexpected(expected) => Self::Unexpected { expected },
            InvalidNot(np) => Self::InvalidNot(np),
            InvalidInteger => Self::InvalidInteger,
            MultipleRootPredicates => Self::MultipleRootPredicates,
            InvalidHasAtomic => Self::InvalidHasAtomic,
            UnknownBuiltin => Self::UnknownBuiltin,
        }
    }
}

impl fmt::Display for ExpressionParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use ExpressionParseErrorKind::*;

        match self {
            InvalidCharacters => f.write_str("invalid character(s)"),
            UnclosedParens => f.write_str("unclosed parens"),
            UnopenedParens => f.write_str("unopened parens"),
            UnclosedQuotes => f.write_str("unclosed quotes"),
            UnopenedQuotes => f.write_str("unopened quotes"),
            Empty => f.write_str("empty expression"),
            Unexpected { expected } => {
                if expected.len() > 1 {
                    f.write_str("expected one of ")?;

                    for (i, exp) in expected.iter().enumerate() {
                        f.write_fmt(format_args!("{}`{exp}`", if i > 0 { ", " } else { "" }))?;
                    }
                    f.write_str(" here")
                } else if !expected.is_empty() {
                    f.write_fmt(format_args!("expected a `{}` here", expected[0]))
                } else {
                    f.write_str("the term was not expected here")
                }
            }
            InvalidNot(np) => f.write_fmt(format_args!("not() takes 1 predicate, found {np}")),
            InvalidInteger => f.write_str("invalid integer"),
            MultipleRootPredicates => f.write_str("multiple root predicates"),
            InvalidHasAtomic => f.write_str("expected integer or \"ptr\""),
            UnknownBuiltin => f.write_str("unknown built-in"),
        }
    }
}

/// An error that occurred while parsing a [`TargetSpecPlainString`](crate::TargetSpecPlainString).
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct PlainStringParseError {
    /// The input we failed to parse.
    pub input: String,

    /// The character index (in bytes) at which the input failed to parse.
    pub char_index: usize,

    /// The character that failed to parse.
    pub character: char,
}

impl PlainStringParseError {
    pub(crate) fn new(input: String, char_index: usize, character: char) -> Self {
        Self {
            input,
            char_index,
            character,
        }
    }

    /// Returns the range of characters in the input that resulted in this error.
    pub fn span(&self) -> std::ops::Range<usize> {
        let end = self.char_index + self.character.len_utf8();
        self.char_index..end
    }
}

impl fmt::Display for PlainStringParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "failed to parse `{}` at index {}: character \
             must be alphanumeric, `-`, `_` or `.`",
            self.input, self.char_index,
        )
    }
}

impl error::Error for PlainStringParseError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        None
    }
}

/// An error returned while parsing a single target.
///
/// This is produced when both of the following are true:
///
/// 1. The triple is not in the builtin set.
/// 2. If heuristic parsing is enabled, it failed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TripleParseError {
    triple_str: Cow<'static, str>,
    kind: TripleParseErrorKind,
}

impl TripleParseError {
    pub(crate) fn new(
        triple_str: Cow<'static, str>,
        lexicon_err: cfg_expr::target_lexicon::ParseError,
    ) -> Self {
        Self {
            triple_str,
            kind: TripleParseErrorKind::Lexicon(lexicon_err),
        }
    }

    pub(crate) fn new_strict(triple_str: Cow<'static, str>) -> Self {
        Self {
            triple_str,
            kind: TripleParseErrorKind::LexiconDisabled,
        }
    }

    /// Returns the triple string that could not be parsed.
    pub fn triple_str(&self) -> &str {
        &self.triple_str
    }
}

impl fmt::Display for TripleParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "unknown triple string: {}", self.triple_str)
    }
}

impl error::Error for TripleParseError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        Some(&self.kind)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TripleParseErrorKind {
    Lexicon(cfg_expr::target_lexicon::ParseError),
    LexiconDisabled,
}

impl fmt::Display for TripleParseErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Lexicon(_) => write!(
                f,
                "triple not in builtin platforms and heuristic parsing failed"
            ),
            Self::LexiconDisabled => write!(
                f,
                "triple not in builtin platforms and heuristic parsing disabled"
            ),
        }
    }
}

impl error::Error for TripleParseErrorKind {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::Lexicon(error) => Some(error),
            Self::LexiconDisabled => None,
        }
    }
}

/// An error returned while creating a custom platform.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum CustomTripleCreateError {
    #[cfg(feature = "custom")]
    /// Deprecated, and no longer used: instead, use [`Self::DeserializeJson`].
    #[deprecated(
        since = "3.3.0",
        note = "this variant is no longer returned: instead, \
                use DeserializeJson which also includes the input string"
    )]
    #[doc(hidden)]
    Deserialize {
        /// The specified triple.
        triple: String,

        /// The deserialization error that occurred.
        error: std::sync::Arc<serde_json::Error>,
    },

    /// A custom platform was asked to be created, but the `custom` feature is currently disabled.
    ///
    /// Currently, this can only happen if a custom platform is deserialized from a
    /// [`PlatformSummary`](crate::summaries::PlatformSummary),
    Unavailable,

    #[cfg(feature = "custom")]
    /// An error occurred while deserializing serde data.
    DeserializeJson {
        /// The specified triple.
        triple: String,

        /// The input string that caused the error.
        input: String,

        /// The deserialization error that occurred.
        error: std::sync::Arc<serde_json::Error>,
    },
}

impl CustomTripleCreateError {
    /// Returns the provided input that caused the error, if available.
    #[inline]
    pub fn input(&self) -> Option<&str> {
        self.input_string().map(String::as_str)
    }

    /// A version of [`Self::input`] that returns a `&String` rather than a
    /// `&str`.
    ///
    /// This is a workaround for a miette limitation -- `&str` can't be cast to
    /// `&dyn SourceCode`, but `&String` can.
    pub fn input_string(&self) -> Option<&String> {
        match self {
            #[cfg(feature = "custom")]
            Self::DeserializeJson { input, .. } => Some(input),
            #[cfg(feature = "custom")]
            #[allow(deprecated)]
            Self::Deserialize { .. } => None,
            Self::Unavailable => None,
        }
    }

    /// Returns the line and column number that caused the error, if available
    /// and the error is not an I/O error.
    ///
    /// The line and column number are 1-based, though the column number can be
    /// 0 if the error occurred between lines.
    #[inline]
    pub fn line_and_column(&self) -> Option<(usize, usize)> {
        match self {
            #[cfg(feature = "custom")]
            Self::DeserializeJson { error, .. } => Some((error.line(), error.column())),
            #[cfg(feature = "custom")]
            #[allow(deprecated)]
            Self::Deserialize { .. } => None,
            Self::Unavailable => None,
        }
    }

    /// Returns a label suitable for the error message to label at
    /// [`Self::line_and_column`].
    ///
    /// This label drops line and column information if available.
    pub fn label(&self) -> Option<String> {
        match self {
            #[cfg(feature = "custom")]
            Self::DeserializeJson { error, .. } => {
                let label = error.to_string();
                // serde_json appends " at line M column N" -- remove it.
                let trimmed = match label.rfind(" at line ") {
                    Some(idx) => label[..idx].to_string(),
                    None => label,
                };
                Some(trimmed)
            }
            #[cfg(feature = "custom")]
            #[allow(deprecated)]
            Self::Deserialize { .. } => None,
            Self::Unavailable => None,
        }
    }
}

impl fmt::Display for CustomTripleCreateError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            #[cfg(feature = "custom")]
            #[allow(deprecated)]
            Self::DeserializeJson { triple, .. } | Self::Deserialize { triple, .. } => {
                write!(f, "error deserializing custom target JSON for `{triple}`")
            }
            Self::Unavailable => {
                write!(
                    f,
                    "custom platforms are currently unavailable: \
                     to enable them, add the `custom` feature to target-spec"
                )
            }
        }
    }
}

impl error::Error for CustomTripleCreateError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            #[cfg(feature = "custom")]
            #[allow(deprecated)]
            Self::DeserializeJson { error, .. } | Self::Deserialize { error, .. } => Some(error),
            Self::Unavailable => None,
        }
    }
}

/// An error occurred while parsing `rustc -vV` output.
///
/// Returned by [`Platform::from_rustc_version_verbose`](crate::Platform::from_rustc_version_verbose).
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum RustcVersionVerboseParseError {
    /// The output was invalid UTF-8.
    InvalidUtf8(FromUtf8Error),

    /// The output did not contain a `host: ` line.
    MissingHostLine {
        /// The output that was parsed.
        output: String,
    },
}

impl fmt::Display for RustcVersionVerboseParseError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RustcVersionVerboseParseError::InvalidUtf8(_) => {
                write!(f, "output from `rustc -vV` was not valid UTF-8")
            }
            RustcVersionVerboseParseError::MissingHostLine { output } => {
                write!(
                    f,
                    "output from `rustc -vV` did not contain a `host: ` line; output:\n---\n{output}---"
                )
            }
        }
    }
}

impl error::Error for RustcVersionVerboseParseError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            RustcVersionVerboseParseError::InvalidUtf8(err) => Some(err),
            RustcVersionVerboseParseError::MissingHostLine { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{TargetSpecExpression, TargetSpecPlainString};
    use test_case::test_case;

    #[test_case("cfg()", 4..4; "empty expression results in span inside cfg")]
    #[test_case("target_os = \"macos", 12..18; "unclosed quote specified without cfg")]
    fn test_expression_parse_error_span(input: &str, expected_span: std::ops::Range<usize>) {
        let err = TargetSpecExpression::new(input).unwrap_err();
        assert_eq!(err.span, expected_span);
    }

    #[test_case("foobar$", 6..7; "dollar sign at end of string")]
    #[test_case("my🛑triple", 2..6; "multibyte character")]
    fn test_plain_string_parse_error_span(input: &str, expected_span: std::ops::Range<usize>) {
        let err = TargetSpecPlainString::new(input.to_owned()).unwrap_err();
        assert_eq!(err.span(), expected_span);
    }
}
