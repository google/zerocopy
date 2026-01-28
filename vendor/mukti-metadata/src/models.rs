// Copyright (c) The mukti Contributors
// SPDX-License-Identifier: MIT or Apache-2.0

use crate::VersionRangeParseError;
use semver::{Version, VersionReq};
use serde::{de::Visitor, ser::SerializeMap, Deserialize, Serialize, Serializer};
use std::{borrow::Cow, collections::BTreeMap, fmt, str::FromStr};

#[derive(Clone, Debug, Default, Deserialize, Serialize)]
pub struct MuktiReleasesJson {
    /// The projects that are part of this releases.json.
    pub projects: BTreeMap<String, MuktiProject>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct MuktiProject {
    /// The latest version range (key in the releases field) without any pre-releases.
    pub latest: Option<VersionRange>,

    /// Map of version range (major or minor version) to release data about it
    #[serde(serialize_with = "serialize_reverse")]
    pub ranges: BTreeMap<VersionRange, ReleaseRangeData>,
}

impl MuktiProject {
    /// Return all version data for this release, ordered by most recent version first.
    ///
    /// Includes pre-release and yanked versions.
    pub fn all_versions(&self) -> impl Iterator<Item = (&Version, &ReleaseVersionData)> {
        self.ranges
            .values()
            .rev()
            .flat_map(|range| range.versions.iter().rev())
    }

    /// Retrieve data for this exact version if found.
    ///
    /// Can include yanked or pre-release versions.
    pub fn get_version_data(&self, version: &Version) -> Option<(&Version, &ReleaseVersionData)> {
        // Ignore build metadata since it isn't relevant.
        self.all_versions()
            .find(|&(v2, _)| eq_ignoring_build_metadata(version, v2))
    }

    /// Retrieve the latest version that matches this `VersionReq`.
    ///
    /// This will match the latest non-pre-release, non-yanked version.
    pub fn get_latest_matching(&self, req: &VersionReq) -> Option<(&Version, &ReleaseVersionData)> {
        self.all_versions().find(|&(version, version_data)| {
            version_data.status == ReleaseStatus::Active && req.matches(version)
        })
    }
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ReleaseRangeData {
    /// The latest version within this range (can be a prerelease)
    pub latest: Version,

    /// True if this version range only has prereleases.
    pub is_prerelease: bool,

    /// All known versions
    #[serde(serialize_with = "serialize_reverse")]
    pub versions: BTreeMap<Version, ReleaseVersionData>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ReleaseVersionData {
    /// Canonical URL for this release
    pub release_url: String,

    /// The status of a release
    pub status: ReleaseStatus,

    /// Release locations
    pub locations: Vec<ReleaseLocation>,

    /// Custom domain-specific information stored about this release.
    #[serde(default)]
    pub metadata: serde_json::Value,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Deserialize, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum ReleaseStatus {
    /// This release is active.
    Active,

    /// This release was yanked.
    Yanked,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
pub struct ReleaseLocation {
    /// The target string
    pub target: String,

    /// The archive format (e.g. ".tar.gz" or ".zip")
    pub format: String,

    /// The URL the target can be downloaded at
    pub url: String,

    /// The checksums for the target as a map of algorithm to checksum. This is
    /// left open-ended to allow for new checksum algorithms to be added in the
    /// future.
    #[serde(default)]
    pub checksums: BTreeMap<DigestAlgorithm, Digest>,
}

#[derive(Clone, Debug, Deserialize, Serialize, PartialEq, Eq, PartialOrd, Ord)]
#[serde(transparent)]
pub struct DigestAlgorithm(Cow<'static, str>);

impl DigestAlgorithm {
    /// The SHA-256 checksum algorithm.
    pub const SHA256: Self = Self(Cow::Borrowed("sha256"));

    /// The BLAKE2b-512 checksum algorithm.
    pub const BLAKE2B: Self = Self(Cow::Borrowed("blake2b"));

    pub const fn new_static(algorithm: &'static str) -> Self {
        Self(Cow::Borrowed(algorithm))
    }

    pub fn new(algorithm: String) -> Self {
        Self(Cow::Owned(algorithm))
    }
}

/// A digest, typically encoded as a hex string.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(transparent)]
pub struct Digest(pub String);

fn serialize_reverse<S, K, V>(map: &BTreeMap<K, V>, serializer: S) -> Result<S::Ok, S::Error>
where
    S: Serializer,
    K: Serialize,
    V: Serialize,
{
    let mut serialize_map = serializer.serialize_map(Some(map.len()))?;
    for (k, v) in map.iter().rev() {
        serialize_map.serialize_entry(k, v)?;
    }
    serialize_map.end()
}

/// Represents a range of versions
#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum VersionRange {
    Patch(u64),
    Minor(u64),
    Major(u64),
}

impl VersionRange {
    pub fn from_version(version: &Version) -> Self {
        if version.major >= 1 {
            VersionRange::Major(version.major)
        } else if version.minor >= 1 {
            VersionRange::Minor(version.minor)
        } else {
            VersionRange::Patch(version.patch)
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, PartialOrd, Ord, Hash)]
pub enum VersionRangeKind {
    /// Patch version.
    Patch,
    /// Minor version.
    Minor,
    /// Major version.
    Major,
}

impl VersionRangeKind {
    pub fn description(&self) -> &'static str {
        match self {
            Self::Major => "major",
            Self::Minor => "minor",
            Self::Patch => "patch",
        }
    }
}

impl fmt::Display for VersionRange {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Major(major) => write!(f, "{}", major),
            Self::Minor(minor) => write!(f, "0.{}", minor),
            Self::Patch(patch) => write!(f, "0.0.{}", patch),
        }
    }
}

impl FromStr for VersionRange {
    type Err = VersionRangeParseError;

    fn from_str(input: &str) -> Result<Self, Self::Err> {
        if let Some(patch_str) = input.strip_prefix("0.0.") {
            parse_component(patch_str, VersionRangeKind::Patch).map(Self::Patch)
        } else if let Some(minor_str) = input.strip_prefix("0.") {
            parse_component(minor_str, VersionRangeKind::Minor).map(Self::Minor)
        } else {
            parse_component(input, VersionRangeKind::Major).map(Self::Major)
        }
    }
}

fn parse_component(s: &str, component: VersionRangeKind) -> Result<u64, VersionRangeParseError> {
    s.parse()
        .map_err(|err| VersionRangeParseError::new(s, component, err))
}

impl Serialize for VersionRange {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_str(&format!("{}", self))
    }
}

impl<'de> Deserialize<'de> for VersionRange {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        deserializer.deserialize_str(VersionRangeDeVisitor)
    }
}

struct VersionRangeDeVisitor;

impl<'de> Visitor<'de> for VersionRangeDeVisitor {
    type Value = VersionRange;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(
            formatter,
            "a version range in the format major, major.minor, or major.minor.patch"
        )
    }

    fn visit_str<E>(self, s: &str) -> Result<Self::Value, E>
    where
        E: serde::de::Error,
    {
        s.parse().map_err(|err| E::custom(err))
    }
}

#[inline]
fn eq_ignoring_build_metadata(a: &Version, b: &Version) -> bool {
    a.major == b.major && a.minor == b.minor && a.patch == b.patch && a.pre == b.pre
}

#[cfg(test)]
mod tests {
    use super::*;

    static FIXTURE_JSON: &str = include_str!("../../fixtures/mukti-releases.json");

    #[test]
    fn test_get_version_data() {
        let json: MuktiReleasesJson = serde_json::from_str(FIXTURE_JSON).unwrap();
        let project = &json.projects["mukti"];
        // Active version matches
        assert_eq!(
            get_version_data(project, "0.5.3").release_url,
            "https://my-release-url/version-0.5.3",
            "data for active version 0.5.3 matches"
        );
        // Yanked version still matches.
        assert_eq!(
            get_version_data(project, "0.5.2").release_url,
            "https://my-release-url/version-0.5.2",
            "data for yanked version 0.5.2 matches"
        );
        // Pre-release version matches.
        assert_eq!(
            get_version_data(project, "0.6.0-alpha.1").release_url,
            "https://my-release-url/version-0.6.0-alpha.1",
            "data for pre-release 0.6.0-alpha.1 matches"
        );
    }

    #[track_caller]
    fn version(version_str: &str) -> Version {
        Version::parse(version_str)
            .unwrap_or_else(|err| panic!("unable to parse version string {version_str}: {err}"))
    }

    fn get_version_data<'a>(
        project: &'a MuktiProject,
        version_str: &str,
    ) -> &'a ReleaseVersionData {
        let version = version(version_str);
        let (_, version_data) = project
            .get_version_data(&version)
            .unwrap_or_else(|| panic!("no version data found for {version_str}"));
        version_data
    }

    #[test]
    fn test_get_latest_matching() {
        let json: MuktiReleasesJson = serde_json::from_str(FIXTURE_JSON).unwrap();
        let project = &json.projects["mukti"];

        // Latest version.
        assert_eq!(
            get_latest_matching_version(project, "*"),
            Some(&version("0.5.3")),
            "latest non-prerelease version"
        );
        assert_eq!(
            get_latest_matching_version(project, "0.5"),
            Some(&version("0.5.3")),
            "latest version in the 0.5 series"
        );

        // Version matching only pre-releases.
        assert_eq!(
            get_latest_matching_version(project, "0.6"),
            None,
            "0.6.0-alpha.1, being a pre-release, should not match 0.6.0"
        );

        // Version matching pre-release.
        assert_eq!(
            get_latest_matching_version(project, "0.6.0-alpha.1"),
            Some(&version("0.6.0-alpha.1")),
            "0.6.0-alpha.1 is a pre-release that matches this comparator"
        );

        // 0.5.2 is yanked.
        assert_eq!(
            get_latest_matching_version(project, "^0.5,<0.5.3"),
            Some(&version("0.5.1")),
            "0.5.2 is yanked so 0.5.1 should be returned"
        );
    }

    fn get_latest_matching_version<'a>(
        project: &'a MuktiProject,
        version_req_str: &str,
    ) -> Option<&'a Version> {
        let version_req = VersionReq::parse(version_req_str).unwrap();
        let (version, _) = project.get_latest_matching(&version_req)?;
        Some(version)
    }
}
