// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    Error, Platform, Triple,
    errors::{ExpressionParseError, PlainStringParseError},
};
use cfg_expr::{Expression, Predicate};
use std::{borrow::Cow, fmt, str::FromStr, sync::Arc};

/// A parsed target specification or triple string, as found in a `Cargo.toml` file.
///
/// ## Expressions and triple strings
///
/// Cargo supports [platform-specific
/// dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#platform-specific-dependencies).
/// These dependencies can be specified in one of two ways:
///
/// ```toml
/// # 1. As Rust-like `#[cfg]` syntax.
/// [target.'cfg(all(unix, target_arch = "x86_64"))'.dependencies]
/// native = { path = "native/x86_64" }
///
/// # 2. Listing out the full target triple.
/// [target.x86_64-pc-windows-gnu.dependencies]
/// winhttp = "0.4.0"
/// ```
///
/// ### The `cfg()` syntax
///
/// The first [`cfg()` syntax](https://doc.rust-lang.org/reference/conditional-compilation.html) is
/// represented via the [`TargetSpec::Expression`] variant. This variant represents an arbitrary
/// expression against certain properties of the target. To evaluate a [`Platform`] against this
/// variant, `target-spec` builds an expression tree (currently via
/// [`cfg-expr`](https://github.com/EmbarkStudios/cfg-expr)).
///
/// ### Plain string syntax
///
/// The second syntax, listing just the name of a platform, is represented via the
/// [`TargetSpec::PlainString`] variant. In target-spec's model, the contained data is arbitrary
/// and used only for string comparisons. For example,
/// `TargetSpec::PlainString("x86_64-pc-windows-gnu")` will match the `x86_64-pc-windows-gnu`
/// platform.
///
/// `target-spec` checks that the string looks sufficiently like a triple. This check is duplicated
/// from Cargo's own check and is implemented in [`Self::looks_like_plain_string`].
///
/// ## Examples
///
/// ```
/// use target_spec::{Platform, TargetFeatures, TargetSpec};
///
/// let i686_windows = Platform::new("i686-pc-windows-gnu", TargetFeatures::Unknown).unwrap();
/// let x86_64_mac = Platform::new("x86_64-apple-darwin", TargetFeatures::none()).unwrap();
/// let i686_linux = Platform::new(
///     "i686-unknown-linux-gnu",
///     TargetFeatures::features(["sse2"].iter().copied()),
/// ).unwrap();
///
/// let spec: TargetSpec = "cfg(any(windows, target_arch = \"x86_64\"))".parse().unwrap();
/// assert_eq!(spec.eval(&i686_windows), Some(true), "i686 Windows");
/// assert_eq!(spec.eval(&x86_64_mac), Some(true), "x86_64 MacOS");
/// assert_eq!(spec.eval(&i686_linux), Some(false), "i686 Linux (should not match)");
///
/// let spec: TargetSpec = "cfg(any(target_feature = \"sse2\", target_feature = \"sse\"))".parse().unwrap();
/// assert_eq!(spec.eval(&i686_windows), None, "i686 Windows features are unknown");
/// assert_eq!(spec.eval(&x86_64_mac), Some(false), "x86_64 MacOS matches no features");
/// assert_eq!(spec.eval(&i686_linux), Some(true), "i686 Linux matches some features");
/// ```
#[derive(Clone, Debug)]
pub enum TargetSpec {
    /// A complex expression.
    ///
    /// Parsed from strings like `"cfg(any(windows, target_arch = \"x86_64\"))"`.
    Expression(TargetSpecExpression),

    /// A plain string representing a triple.
    ///
    /// This string hasn't been validated because it may represent a custom platform. To validate
    /// this string, use [`Self::is_known`].
    PlainString(TargetSpecPlainString),
}

impl TargetSpec {
    /// Creates a new target spec from a string.
    pub fn new(input: impl Into<Cow<'static, str>>) -> Result<Self, Error> {
        let input = input.into();

        if Self::looks_like_expression(&input) {
            match TargetSpecExpression::new(&input) {
                Ok(expression) => Ok(Self::Expression(expression)),
                Err(error) => Err(Error::InvalidExpression(error)),
            }
        } else {
            match TargetSpecPlainString::new(input) {
                Ok(plain_str) => Ok(Self::PlainString(plain_str)),
                Err(error) => Err(Error::InvalidTargetSpecString(error)),
            }
        }
    }

    /// Returns true if the input will be parsed as a target expression.
    ///
    /// In other words, returns true if the input begins with `"cfg("`.
    pub fn looks_like_expression(input: &str) -> bool {
        input.starts_with("cfg(")
    }

    /// Returns true if the input will be understood to be a plain string.
    ///
    /// This check is borrowed from
    /// [`cargo-platform`](https://github.com/rust-lang/cargo/blob/5febbe5587b74108165f748e79a4f8badbdf5e0e/crates/cargo-platform/src/lib.rs#L40-L63).
    ///
    /// Note that this currently accepts an empty string. This matches Cargo's behavior as of Rust
    /// 1.70.
    pub fn looks_like_plain_string(input: &str) -> bool {
        TargetSpecPlainString::validate(input).is_ok()
    }

    /// Returns true if an input looks like it's known and understood.
    ///
    /// * For [`Self::Expression`], the inner [`TargetSpecExpression`] has already been parsed as
    ///   valid, so this returns true.
    /// * For [`Self::PlainString`], this returns true if the string matches a builtin triple or has
    ///   heuristically been determined to be valid.
    ///
    /// This method does not take into account custom platforms. If you know about custom platforms,
    /// consider checking against those as well.
    pub fn is_known(&self) -> bool {
        match self {
            TargetSpec::PlainString(plain_str) => {
                Triple::new(plain_str.as_str().to_owned()).is_ok()
            }
            TargetSpec::Expression(_) => true,
        }
    }

    /// Evaluates this specification against the given platform.
    ///
    /// Returns `Some(true)` if there's a match, `Some(false)` if there's none, or `None` if the
    /// result of the evaluation is unknown (typically found if target features are involved).
    #[inline]
    pub fn eval(&self, platform: &Platform) -> Option<bool> {
        match self {
            TargetSpec::PlainString(plain_str) => Some(platform.triple_str() == plain_str.as_str()),
            TargetSpec::Expression(expr) => expr.eval(platform),
        }
    }
}

impl FromStr for TargetSpec {
    type Err = Error;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Self::new(input.to_owned())
    }
}

impl fmt::Display for TargetSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TargetSpec::Expression(expr) => write!(f, "{expr}"),
            TargetSpec::PlainString(plain_str) => write!(f, "{plain_str}"),
        }
    }
}

/// A target expression, parsed from a string beginning with `cfg(`.
///
/// For more information, see [`TargetSpec`].
#[derive(Clone, Debug)]
pub struct TargetSpecExpression {
    inner: Arc<Expression>,
}

impl TargetSpecExpression {
    /// Creates a new `TargetSpecExpression` from a string beginning with `cfg(`.
    ///
    /// Returns an error if the string could not be parsed, or if the string contains a predicate
    /// that wasn't understood by `target-spec`.
    pub fn new(input: &str) -> Result<Self, ExpressionParseError> {
        let expr = Expression::parse(input).map_err(|err| ExpressionParseError::new(input, err))?;
        Ok(Self {
            inner: Arc::new(expr),
        })
    }

    /// Returns the string that was parsed into `self`.
    #[inline]
    pub fn expression_str(&self) -> &str {
        self.inner.original()
    }

    /// Evaluates this expression against the given platform.
    ///
    /// Returns `Some(true)` if there's a match, `Some(false)` if there's none, or `None` if the
    /// result of the evaluation is unknown (typically found if target features are involved).
    pub fn eval(&self, platform: &Platform) -> Option<bool> {
        self.inner.eval(|pred| {
            match pred {
                Predicate::Target(target) => Some(platform.triple().matches(target)),
                Predicate::TargetFeature(feature) => platform.target_features().matches(feature),
                Predicate::Test | Predicate::DebugAssertions | Predicate::ProcMacro => {
                    // Known families that always evaluate to false. See
                    // https://docs.rs/cargo-platform/0.1.1/src/cargo_platform/lib.rs.html#76.
                    Some(false)
                }
                Predicate::Feature(_) => {
                    // NOTE: This is not supported by Cargo which always evaluates this to false. See
                    // https://github.com/rust-lang/cargo/issues/7442 for more details.
                    Some(false)
                }
                Predicate::Flag(flag) => {
                    // This returns false by default but true in some cases.
                    Some(platform.has_flag(flag))
                }
                Predicate::KeyValue { .. } => {
                    // This is always interpreted by Cargo as false.
                    Some(false)
                }
            }
        })
    }
}

impl FromStr for TargetSpecExpression {
    type Err = ExpressionParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Self::new(input)
    }
}

impl fmt::Display for TargetSpecExpression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.expression_str())
    }
}

/// A plain string as contained within a [`TargetSpec::PlainString`].
///
/// For more information, see [`TargetSpec`].
#[derive(Clone, Debug)]
pub struct TargetSpecPlainString(Cow<'static, str>);

impl TargetSpecPlainString {
    /// Creates a new instance of `TargetSpecPlainString`, after validating it.
    pub fn new(input: impl Into<Cow<'static, str>>) -> Result<Self, PlainStringParseError> {
        let input = input.into();
        Self::validate(&input)?;
        Ok(Self(input))
    }

    /// Returns the string as parsed.
    pub fn as_str(&self) -> &str {
        &self.0
    }

    fn validate(input: &str) -> Result<(), PlainStringParseError> {
        if let Some((char_index, c)) = input
            .char_indices()
            .find(|&(_, c)| !(c.is_alphanumeric() || c == '_' || c == '-' || c == '.'))
        {
            Err(PlainStringParseError::new(input.to_owned(), char_index, c))
        } else {
            Ok(())
        }
    }
}

impl FromStr for TargetSpecPlainString {
    type Err = PlainStringParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        Self::new(input.to_owned())
    }
}

impl fmt::Display for TargetSpecPlainString {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cfg_expr::{
        Predicate, TargetPredicate,
        targets::{Abi, Arch, Family, Os},
    };

    #[test]
    fn test_triple() {
        let res = TargetSpec::new("x86_64-apple-darwin");
        assert!(matches!(
            res,
            Ok(TargetSpec::PlainString(triple)) if triple.as_str() == "x86_64-apple-darwin"
        ));
    }

    #[test]
    fn test_single() {
        let expr = match TargetSpec::new("cfg(windows)").unwrap() {
            TargetSpec::PlainString(triple) => {
                panic!("expected expression, got triple: {triple:?}")
            }
            TargetSpec::Expression(expr) => expr,
        };
        assert_eq!(
            expr.inner.predicates().collect::<Vec<_>>(),
            vec![Predicate::Target(TargetPredicate::Family(Family::windows))],
        );
    }

    #[test]
    fn test_target_abi() {
        let expr =
            match TargetSpec::new("cfg(any(target_arch = \"wasm32\", target_abi = \"unknown\"))")
                .unwrap()
            {
                TargetSpec::PlainString(triple) => {
                    panic!("expected expression, got triple: {triple:?}")
                }
                TargetSpec::Expression(expr) => expr,
            };

        assert_eq!(
            expr.inner.predicates().collect::<Vec<_>>(),
            vec![
                Predicate::Target(TargetPredicate::Arch(Arch("wasm32".into()))),
                Predicate::Target(TargetPredicate::Abi(Abi("unknown".into()))),
            ],
        );
    }

    #[test]
    fn test_not() {
        assert!(matches!(
            TargetSpec::new("cfg(not(windows))"),
            Ok(TargetSpec::Expression(_))
        ));
    }

    #[test]
    fn test_testequal() {
        let expr = match TargetSpec::new("cfg(target_os = \"windows\")").unwrap() {
            TargetSpec::PlainString(triple) => {
                panic!("expected spec, got triple: {triple:?}")
            }
            TargetSpec::Expression(expr) => expr,
        };

        assert_eq!(
            expr.inner.predicates().collect::<Vec<_>>(),
            vec![Predicate::Target(TargetPredicate::Os(Os::windows))],
        );
    }

    #[test]
    fn test_identifier_like_triple() {
        // This used to be "x86_64-pc-darwin", but target-lexicon can parse that.
        let spec = TargetSpec::new("cannotbeknown")
            .expect("triples that look like identifiers should parse correctly");
        assert!(!spec.is_known(), "spec isn't known");
    }

    #[test]
    fn test_triple_string_identifier() {
        // We generally trust that unicode-ident is correct. Just do some basic checks.
        let valid = ["", "foo", "foo-bar", "foo_baz", "-foo", "quux-"];
        let invalid = ["foo+bar", "foo bar", " "];
        for input in valid {
            assert!(
                TargetSpec::looks_like_plain_string(input),
                "`{input}` looks like triple string"
            );
        }
        for input in invalid {
            assert!(
                !TargetSpec::looks_like_plain_string(input),
                "`{input}` does not look like triple string"
            );
        }
    }

    #[test]
    fn test_unknown_triple() {
        // This used to be "x86_64-pc-darwin", but target-lexicon can parse that.
        let err = TargetSpec::new("cannotbeknown!!!")
            .expect_err("unknown triples should parse correctly");
        assert!(matches!(
            err,
            Error::InvalidTargetSpecString(s) if s.input == "cannotbeknown!!!"
        ));
    }

    #[test]
    fn test_unknown_flag() {
        let expr = match TargetSpec::new("cfg(foo)").unwrap() {
            TargetSpec::PlainString(triple) => {
                panic!("expected spec, got triple: {triple:?}")
            }
            TargetSpec::Expression(expr) => expr,
        };

        assert_eq!(
            expr.inner.predicates().collect::<Vec<_>>(),
            vec![Predicate::Flag("foo")],
        );
    }

    #[test]
    fn test_unknown_predicate() {
        let expr = match TargetSpec::new("cfg(bogus_key = \"bogus_value\")")
            .expect("unknown predicate should parse")
        {
            TargetSpec::PlainString(triple) => {
                panic!("expected spec, got triple: {triple:?}")
            }
            TargetSpec::Expression(expr) => expr,
        };
        assert_eq!(
            expr.inner.predicates().collect::<Vec<_>>(),
            vec![Predicate::KeyValue {
                key: "bogus_key",
                val: "bogus_value"
            }],
        );

        let platform = Platform::build_target().unwrap();
        // This should always evaluate to false.
        assert_eq!(expr.eval(&platform), Some(false));

        let expr = TargetSpec::new("cfg(not(bogus_key = \"bogus_value\"))")
            .expect("unknown predicate should parse");
        // This is a cfg(not()), so it should always evaluate to true.
        assert_eq!(expr.eval(&platform), Some(true));
    }

    #[test]
    fn test_extra() {
        let res = TargetSpec::new("cfg(unix)this-is-extra");
        res.expect_err("extra content at the end");
    }

    #[test]
    fn test_incomplete() {
        // This fails because the ) at the end is missing.
        let res = TargetSpec::new("cfg(not(unix)");
        res.expect_err("missing ) at the end");
    }
}
