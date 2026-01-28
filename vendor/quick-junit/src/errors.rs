// Copyright (c) The nextest Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use quick_xml::{encoding::EncodingError, escape::EscapeError, events::attributes::AttrError};
use std::{fmt, io};
use thiserror::Error;

/// An error that occurs while serializing a [`Report`](crate::Report).
///
/// Returned by [`Report::serialize`](crate::Report::serialize) and
/// [`Report::to_string`](crate::Report::to_string).
#[derive(Debug, Error)]
#[error("error serializing JUnit report")]
pub struct SerializeError {
    #[from]
    inner: quick_xml::Error,
}

impl From<EncodingError> for SerializeError {
    fn from(inner: EncodingError) -> Self {
        Self {
            inner: quick_xml::Error::Encoding(inner),
        }
    }
}

impl From<io::Error> for SerializeError {
    fn from(inner: io::Error) -> Self {
        Self {
            inner: quick_xml::Error::from(inner),
        }
    }
}

/// Represents a location in the XML document structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PathElement {
    /// The root `<testsuites>` element
    TestSuites,
    /// A `<testsuite>` element at the given index, with optional name
    TestSuite(usize, Option<String>),
    /// A `<testcase>` element at the given index, with optional name
    TestCase(usize, Option<String>),
    /// The `<properties>` container element
    Properties,
    /// A `<property>` element at the given index
    Property(usize),
    /// A `<failure>` element
    Failure,
    /// An `<error>` element
    Error,
    /// A `<skipped>` element
    Skipped,
    /// A `<flakyFailure>` element
    FlakyFailure,
    /// A `<flakyError>` element
    FlakyError,
    /// A `<rerunFailure>` element
    RerunFailure,
    /// A `<rerunError>` element
    RerunError,
    /// A `<system-out>` element
    SystemOut,
    /// A `<system-err>` element
    SystemErr,
    /// An attribute with the given name
    Attribute(String),
}

impl fmt::Display for PathElement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PathElement::TestSuites => write!(f, "testsuites"),
            PathElement::TestSuite(idx, Some(name)) => {
                write!(f, "testsuite[{}](\"{}\")", idx, name)
            }
            PathElement::TestSuite(idx, None) => write!(f, "testsuite[{}]", idx),
            PathElement::TestCase(idx, Some(name)) => write!(f, "testcase[{}](\"{}\")", idx, name),
            PathElement::TestCase(idx, None) => write!(f, "testcase[{}]", idx),
            PathElement::Properties => write!(f, "properties"),
            PathElement::Property(idx) => write!(f, "property[{}]", idx),
            PathElement::Failure => write!(f, "failure"),
            PathElement::Error => write!(f, "error"),
            PathElement::Skipped => write!(f, "skipped"),
            PathElement::FlakyFailure => write!(f, "flakyFailure"),
            PathElement::FlakyError => write!(f, "flakyError"),
            PathElement::RerunFailure => write!(f, "rerunFailure"),
            PathElement::RerunError => write!(f, "rerunError"),
            PathElement::SystemOut => write!(f, "system-out"),
            PathElement::SystemErr => write!(f, "system-err"),
            PathElement::Attribute(name) => write!(f, "@{}", name),
        }
    }
}

/// The kind of error that occurred during deserialization.
#[derive(Debug, Error)]
#[non_exhaustive]
pub enum DeserializeErrorKind {
    /// An error occurred while parsing XML.
    #[error("error parsing XML")]
    XmlError(#[from] quick_xml::Error),

    /// An error occurred while parsing UTF-8.
    #[error("invalid UTF-8")]
    Utf8Error(#[from] std::str::Utf8Error),

    /// An error occurred while parsing an integer.
    #[error("invalid integer: {0}")]
    ParseIntError(#[from] std::num::ParseIntError),

    /// An error occurred while parsing a float.
    #[error("invalid float: {0}")]
    ParseFloatError(#[from] std::num::ParseFloatError),

    /// An error occurred while parsing a timestamp.
    #[error("invalid timestamp: {0}")]
    ParseTimestampError(String),

    /// An error occurred while parsing a duration.
    #[error("invalid duration: {0}")]
    ParseDurationError(String),

    /// An error occurred while parsing a UUID.
    #[error("invalid UUID: {0}")]
    ParseUuidError(#[from] uuid::Error),

    /// Missing required attribute.
    #[error("missing required attribute: {0}")]
    MissingAttribute(String),

    /// Unexpected XML element.
    #[error("unexpected element: {0}")]
    UnexpectedElement(String),

    /// Invalid XML structure.
    #[error("invalid structure: {0}")]
    InvalidStructure(String),

    /// An I/O error occurred.
    #[error("I/O error")]
    IoError(#[from] io::Error),

    /// An error occurred while parsing XML attributes.
    #[error("attribute error: {0}")]
    AttrError(#[from] AttrError),

    /// An error occurred while unescaping XML entities.
    #[error("XML unescape error: {0}")]
    EscapeError(#[from] EscapeError),
}

/// An error that occurs while deserializing a [`Report`](crate::Report).
///
/// Returned by [`Report::deserialize`](crate::Report::deserialize) and
/// [`Report::deserialize_from_str`](crate::Report::deserialize_from_str).
#[derive(Debug)]
pub struct DeserializeError {
    /// The kind of error that occurred
    kind: DeserializeErrorKind,
    /// The path to the location in the XML document where the error occurred
    path: Vec<PathElement>,
}

impl DeserializeError {
    /// Creates a new error with the given kind and path.
    pub fn new(kind: DeserializeErrorKind, path: Vec<PathElement>) -> Self {
        Self { kind, path }
    }

    /// Returns the kind of error.
    pub fn kind(&self) -> &DeserializeErrorKind {
        &self.kind
    }

    /// Returns the path to the error location.
    pub fn path(&self) -> &[PathElement] {
        &self.path
    }
}

impl fmt::Display for DeserializeError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.path.is_empty() {
            write!(f, "{}", self.kind)
        } else {
            write!(f, "at ")?;
            for (i, element) in self.path.iter().enumerate() {
                if i > 0 {
                    write!(f, "/")?;
                }
                write!(f, "{}", element)?;
            }
            write!(f, ": {}", self.kind)
        }
    }
}

impl std::error::Error for DeserializeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        self.kind.source()
    }
}
