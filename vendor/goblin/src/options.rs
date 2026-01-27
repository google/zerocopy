//! Unified parsing options used across ELF/PE/Mach-O.

/// Binary parsing mode.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParseMode {
    /// Fail on malformed data.
    Strict,
    /// Attempt to recover on malformed data.
    Permissive,
}

impl Default for ParseMode {
    fn default() -> Self {
        ParseMode::Strict
    }
}

impl ParseMode {
    /// True if permissive.
    pub(crate) fn is_permissive(&self) -> bool {
        matches!(self, ParseMode::Permissive)
    }
}

/// Common parsing options.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ParseOptions {
    /// Selected parsing mode.
    pub parse_mode: ParseMode,
}

impl Default for ParseOptions {
    fn default() -> Self {
        ParseOptions {
            parse_mode: ParseMode::Strict,
        }
    }
}

impl ParseOptions {
    /// Defaults (strict).
    pub fn new() -> Self {
        Default::default()
    }

    /// Permissive defaults.
    pub fn permissive() -> Self {
        ParseOptions {
            parse_mode: ParseMode::Permissive,
        }
    }

    /// Strict defaults.
    pub fn strict() -> Self {
        ParseOptions {
            parse_mode: ParseMode::Strict,
        }
    }

    /// Set parse mode.
    pub fn with_parse_mode(mut self, parse_mode: ParseMode) -> Self {
        self.parse_mode = parse_mode;
        self
    }
}

/// Internal helper trait for permissive fallbacks on `Result<T, E>`.
pub(crate) trait Permissive<T, E> {
    fn or_permissive_and_default(
        self,
        permissive: bool,
        context: &str,
    ) -> core::result::Result<T, E>;

    #[allow(unused)]
    fn or_permissive_and_value(
        self,
        permissive: bool,
        context: &str,
        value: T,
    ) -> core::result::Result<T, E>;

    #[allow(unused)]
    fn or_permissive_and_then<F>(
        self,
        permissive: bool,
        context: &str,
        f: F,
    ) -> core::result::Result<T, E>
    where
        F: FnOnce() -> T;

    // Note: use static context messages to avoid allocations on success path.
}

impl<T: Default, E: core::fmt::Display> Permissive<T, E> for core::result::Result<T, E> {
    #[allow(unused)]
    fn or_permissive_and_default(
        self,
        permissive: bool,
        context: &str,
    ) -> core::result::Result<T, E> {
        self.or_else(|e| {
            if permissive {
                #[cfg(feature = "log")]
                log::warn!("{context}: {e}, continuing with empty/default value");
                Ok(T::default())
            } else {
                Err(e)
            }
        })
    }

    #[allow(unused)]
    fn or_permissive_and_value(
        self,
        permissive: bool,
        context: &str,
        value: T,
    ) -> core::result::Result<T, E> {
        self.or_else(|e| {
            if permissive {
                #[cfg(feature = "log")]
                log::warn!("{context}: {e}, continuing with provided value");
                Ok(value)
            } else {
                Err(e)
            }
        })
    }

    // No lazy-with-ctx variants (keeps this impl alloc-free).

    #[allow(unused)]
    fn or_permissive_and_then<F>(
        self,
        permissive: bool,
        context: &str,
        f: F,
    ) -> core::result::Result<T, E>
    where
        F: FnOnce() -> T,
    {
        self.or_else(|e| {
            if permissive {
                #[cfg(feature = "log")]
                log::warn!("{context}: {e}, continuing with computed value");
                Ok(f())
            } else {
                Err(e)
            }
        })
    }

    // No lazy-with-ctx variants.
}
