use std::ffi::{OsStr, OsString};
use std::fmt;
use std::fmt::{Debug, Formatter};
use std::hash::{Hash, Hasher};

/// An [`OsString`] that's case-insensitive on Windows, used for environment variable names.
#[derive(Clone)]
pub(crate) struct EnvNameString(OsString);

impl Debug for EnvNameString {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl<T: Into<OsString>> From<T> for EnvNameString {
    fn from(name: T) -> Self {
        EnvNameString(name.into())
    }
}

impl AsRef<OsStr> for EnvNameString {
    fn as_ref(&self) -> &OsStr {
        &self.0
    }
}

impl PartialEq<Self> for EnvNameString {
    fn eq(&self, other: &Self) -> bool {
        // On Windows, env var names are case-insensitive
        #[cfg(windows)]
        match (self.0.to_str(), other.0.to_str()) {
            (Some(s1), Some(s2)) => s1.eq_ignore_ascii_case(s2),
            // If either name isn't valid Unicode then just leave it as is.
            _ => self.0 == other.0,
        }

        // On all other platforms, env var names are case-sensitive.
        #[cfg(not(windows))]
        {
            self.0 == other.0
        }
    }
}

impl Eq for EnvNameString {}

impl Hash for EnvNameString {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // On Windows, env var names are case-insensitive
        #[cfg(windows)]
        match self.0.to_str() {
            Some(s) => {
                // Uppercase each byte separately to avoid reallocating. This is similar to what
                // eq_ignore_ascii_case does internally.
                for &b in s.as_bytes() {
                    b.to_ascii_uppercase().hash(state);
                }
            }
            // If the name isn't valid Unicode then just leave it as is.
            None => self.0.hash(state),
        }

        // On all other platforms, env var names are case-sensitive.
        #[cfg(not(windows))]
        {
            self.0.hash(state);
        }
    }
}

#[cfg(windows)]
#[test]
fn test_env_name_string_windows() {
    let strings1 = [
        EnvNameString::from("abc"),
        EnvNameString::from("Abc"),
        EnvNameString::from("aBc"),
        EnvNameString::from("abC"),
        EnvNameString::from("ABc"),
        EnvNameString::from("aBC"),
        EnvNameString::from("AbC"),
        EnvNameString::from("ABC"),
    ];
    let strings2 = [
        EnvNameString::from("xyz"),
        EnvNameString::from("Xyz"),
        EnvNameString::from("xYz"),
        EnvNameString::from("xyZ"),
        EnvNameString::from("XYz"),
        EnvNameString::from("xYZ"),
        EnvNameString::from("XyZ"),
        EnvNameString::from("XYZ"),
    ];
    // All the strings in `strings1` compare equal to each other and hash the same on Windows.
    for s1 in &strings1 {
        for also_s1 in &strings1 {
            assert_eq!(s1, also_s1);
            let mut hash_set = std::collections::HashSet::new();
            hash_set.insert(s1);
            hash_set.insert(also_s1);
            assert_eq!(hash_set.len(), 1);
        }
    }
    // Same for `strings2`.
    for s2 in &strings2 {
        for also_s2 in &strings2 {
            assert_eq!(s2, also_s2);
            let mut hash_set = std::collections::HashSet::new();
            hash_set.insert(s2);
            hash_set.insert(also_s2);
            assert_eq!(hash_set.len(), 1);
        }
    }
    // But nothing in `strings1` compares equal to anything in `strings2`. We also assert that
    // their hashes are distinct. In theory they could collide, but using DefaultHasher here (which
    // is initialized with the zero key) should prevent that from happening randomly.
    for s1 in &strings1 {
        for s2 in &strings2 {
            assert_ne!(s1, s2);
            let mut hasher1 = std::hash::DefaultHasher::new();
            s1.hash(&mut hasher1);
            let mut hasher2 = std::hash::DefaultHasher::new();
            s2.hash(&mut hasher2);
            assert_ne!(hasher1.finish(), hasher2.finish());
        }
    }
}

#[cfg(not(windows))]
#[test]
fn test_env_name_string_unix() {
    let strings = [
        EnvNameString::from("Abc"),
        EnvNameString::from("aBc"),
        EnvNameString::from("abC"),
        EnvNameString::from("ABc"),
        EnvNameString::from("aBC"),
        EnvNameString::from("AbC"),
        EnvNameString::from("ABC"),
    ];
    // None of these strings compare equal to "abc" on Unix. We also assert that their hashes are
    // distinct. In theory they could collide, but using DefaultHasher here (which is initialized
    // with the zero key) should prevent that from happening randomly.
    for s in &strings {
        assert_ne!(&EnvNameString::from("abc"), s);
        let mut hasher1 = std::hash::DefaultHasher::new();
        EnvNameString::from("abc").hash(&mut hasher1);
        let mut hasher2 = std::hash::DefaultHasher::new();
        s.hash(&mut hasher2);
        assert_ne!(hasher1.finish(), hasher2.finish());
    }
}
