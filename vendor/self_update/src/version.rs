/*! Semver version checks

The following functions compare two semver compatible version strings.
*/
use crate::errors::*;
use semver::Version;

/// Check if a version is greater than the current
pub fn bump_is_greater(current: &str, other: &str) -> Result<bool> {
    Ok(Version::parse(other)? > Version::parse(current)?)
}

/// Check if a new version is compatible with the current
pub fn bump_is_compatible(current: &str, other: &str) -> Result<bool> {
    let current = Version::parse(current)?;
    let other = Version::parse(other)?;
    Ok(if !current.pre.is_empty() {
        current.major == other.major
            && ((other.minor >= current.minor)
                || (current.minor == other.minor && other.patch >= current.patch))
    } else if other.major == 0 && current.major == 0 {
        current.minor == other.minor && other.patch > current.patch && other.pre.is_empty()
    } else if other.major > 0 {
        current.major == other.major
            && ((other.minor > current.minor)
                || (current.minor == other.minor && other.patch > current.patch))
            && other.pre.is_empty()
    } else {
        false
    })
}

/// Check if a new version is a major bump
pub fn bump_is_major(current: &str, other: &str) -> Result<bool> {
    let current = Version::parse(current)?;
    let other = Version::parse(other)?;
    Ok(other.major > current.major)
}

/// Check if a new version is a minor bump
pub fn bump_is_minor(current: &str, other: &str) -> Result<bool> {
    let current = Version::parse(current)?;
    let other = Version::parse(other)?;
    Ok(current.major == other.major && other.minor > current.minor)
}

/// Check if a new version is a patch bump
pub fn bump_is_patch(current: &str, other: &str) -> Result<bool> {
    let current = Version::parse(current)?;
    let other = Version::parse(other)?;
    Ok(current.major == other.major && current.minor == other.minor && other.patch > current.patch)
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_bump_greater() {
        assert!(bump_is_greater("1.2.0", "1.2.3").unwrap());
        assert!(bump_is_greater("0.2.0", "1.2.3").unwrap());
        assert!(bump_is_greater("0.2.0", "0.2.3").unwrap());
    }

    #[test]
    fn test_bump_is_compatible() {
        assert!(!bump_is_compatible("1.2.0", "2.3.1").unwrap());
        assert!(!bump_is_compatible("0.2.0", "2.3.1").unwrap());
        assert!(!bump_is_compatible("1.2.3", "3.3.0").unwrap());
        assert!(!bump_is_compatible("1.2.3", "0.2.0").unwrap());
        assert!(!bump_is_compatible("0.2.0", "0.3.0").unwrap());
        assert!(!bump_is_compatible("0.3.0", "0.2.0").unwrap());
        assert!(!bump_is_compatible("1.2.3", "1.1.0").unwrap());
        assert!(!bump_is_compatible("2.0.0", "2.0.0-alpha.1").unwrap());
        assert!(!bump_is_compatible("1.2.3", "2.0.0-alpha.1").unwrap());
        assert!(!bump_is_compatible("2.0.0-alpha.1", "3.0.0").unwrap());

        assert!(bump_is_compatible("1.2.0", "1.2.3").unwrap());
        assert!(bump_is_compatible("0.2.0", "0.2.3").unwrap());
        assert!(bump_is_compatible("1.2.0", "1.3.3").unwrap());
        assert!(bump_is_compatible("2.0.0-alpha.0", "2.0.0-alpha.1").unwrap());
        assert!(bump_is_compatible("2.0.0-alpha.0", "2.0.0").unwrap());
        assert!(bump_is_compatible("2.0.0-alpha.0", "2.0.1").unwrap());
        assert!(bump_is_compatible("2.0.0-alpha.0", "2.1.0").unwrap());
    }

    #[test]
    fn test_bump_is_major() {
        assert!(bump_is_major("1.2.0", "2.3.1").unwrap());
        assert!(bump_is_major("0.2.0", "2.3.1").unwrap());
        assert!(bump_is_major("1.2.3", "3.3.0").unwrap());
        assert!(!bump_is_major("1.2.3", "1.2.0").unwrap());
        assert!(!bump_is_major("1.2.3", "0.2.0").unwrap());
    }

    #[test]
    fn test_bump_is_minor() {
        assert!(!bump_is_minor("1.2.0", "2.3.1").unwrap());
        assert!(!bump_is_minor("0.2.0", "2.3.1").unwrap());
        assert!(!bump_is_minor("1.2.3", "3.3.0").unwrap());
        assert!(bump_is_minor("1.2.3", "1.3.0").unwrap());
        assert!(bump_is_minor("0.2.3", "0.4.0").unwrap());
    }

    #[test]
    fn test_bump_is_patch() {
        assert!(!bump_is_patch("1.2.0", "2.3.1").unwrap());
        assert!(!bump_is_patch("0.2.0", "2.3.1").unwrap());
        assert!(!bump_is_patch("1.2.3", "3.3.0").unwrap());
        assert!(!bump_is_patch("1.2.3", "1.2.3").unwrap());
        assert!(bump_is_patch("1.2.0", "1.2.3").unwrap());
        assert!(bump_is_patch("0.2.3", "0.2.4").unwrap());
    }
}
