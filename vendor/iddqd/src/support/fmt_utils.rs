use core::fmt;

/// Debug impl for a static string without quotes.
pub(crate) struct StrDisplayAsDebug(pub(crate) &'static str);

impl fmt::Debug for StrDisplayAsDebug {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Use the Display formatter to write the string without quotes.
        fmt::Display::fmt(&self.0, f)
    }
}
