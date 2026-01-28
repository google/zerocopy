// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{errors::TargetSpecError, platform::PlatformSpec};
use std::sync::Arc;
pub use target_spec::summaries::{PlatformSummary, TargetFeaturesSummary};

/// A serializable version of [`PlatformSpec`].
///
/// Requires the `summaries` feature to be enabled.
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub enum PlatformSpecSummary {
    /// The intersection of all platforms.
    ///
    /// This is converted to and from [`PlatformSpec::Always`], and is expressed as the string
    /// `"always"`, or as `spec = "always"`.
    ///
    /// # Examples
    ///
    /// Deserialize the string `"always"`.
    ///
    /// ```
    /// # use guppy::platform::PlatformSpecSummary;
    /// let spec: PlatformSpecSummary = serde_json::from_str(r#""always""#).unwrap();
    /// assert_eq!(spec, PlatformSpecSummary::Always);
    /// ```
    ///
    /// Deserialize `spec = "always"`.
    ///
    /// ```
    /// # use guppy::platform::PlatformSpecSummary;
    /// let spec: PlatformSpecSummary = toml::from_str(r#"spec = "always""#).unwrap();
    /// assert_eq!(spec, PlatformSpecSummary::Always);
    /// ```
    Always,

    /// An individual platform.
    ///
    /// This is converted to and from [`PlatformSpec::Platform`], and is serialized as the platform
    /// itself (either a triple string, or a map such as
    /// `{ triple = "x86_64-unknown-linux-gnu", target-features = [] }`).
    ///
    /// # Examples
    ///
    /// Deserialize a target triple.
    ///
    /// ```
    /// # use guppy::platform::{PlatformSummary, PlatformSpecSummary};
    /// # use target_spec::summaries::TargetFeaturesSummary;
    /// # use std::collections::BTreeSet;
    /// let spec: PlatformSpecSummary = serde_json::from_str(r#""x86_64-unknown-linux-gnu""#).unwrap();
    /// assert_eq!(
    ///     spec,
    ///     PlatformSpecSummary::Platform(PlatformSummary::new("x86_64-unknown-linux-gnu")),
    /// );
    /// ```
    ///
    /// Deserialize a target map.
    ///
    /// ```
    /// # use guppy::platform::{PlatformSummary, PlatformSpecSummary};
    /// # use target_spec::summaries::TargetFeaturesSummary;
    /// # use std::collections::BTreeSet;
    /// let spec: PlatformSpecSummary = toml::from_str(r#"
    /// triple = "x86_64-unknown-linux-gnu"
    /// target-features = []
    /// flags = []
    /// "#).unwrap();
    /// assert_eq!(
    ///     spec,
    ///     PlatformSpecSummary::Platform(
    ///         PlatformSummary::new("x86_64-unknown-linux-gnu")
    ///             .with_target_features(TargetFeaturesSummary::Features(BTreeSet::new()))
    ///     )
    /// );
    /// ```
    Platform(PlatformSummary),

    /// The union of all platforms.
    ///
    /// This is converted to and from [`PlatformSpec::Any`], and is serialized as the string
    /// `"any"`.
    ///
    /// This is also the default, since in many cases one desires to compute the union of enabled
    /// dependencies across all platforms.
    ///
    /// # Examples
    ///
    /// Deserialize the string `"any"`.
    ///
    /// ```
    /// # use guppy::platform::PlatformSpecSummary;
    /// let spec: PlatformSpecSummary = serde_json::from_str(r#""any""#).unwrap();
    /// assert_eq!(spec, PlatformSpecSummary::Any);
    /// ```
    ///
    /// Deserialize `spec = "any"`.
    ///
    /// ```
    /// # use guppy::platform::PlatformSpecSummary;
    /// let spec: PlatformSpecSummary = toml::from_str(r#"spec = "any""#).unwrap();
    /// assert_eq!(spec, PlatformSpecSummary::Any);
    /// ```
    #[default]
    Any,
}

impl PlatformSpecSummary {
    /// Creates a new `PlatformSpecSummary` from a [`PlatformSpec`].
    pub fn new(platform_spec: &PlatformSpec) -> Self {
        match platform_spec {
            PlatformSpec::Always => PlatformSpecSummary::Always,
            PlatformSpec::Platform(platform) => {
                PlatformSpecSummary::Platform(platform.to_summary())
            }
            PlatformSpec::Any => PlatformSpecSummary::Any,
        }
    }

    /// Converts `self` to a `PlatformSpec`.
    ///
    /// Returns an `Error` if the platform was unknown.
    pub fn to_platform_spec(&self) -> Result<PlatformSpec, TargetSpecError> {
        match self {
            PlatformSpecSummary::Always => Ok(PlatformSpec::Always),
            PlatformSpecSummary::Platform(platform) => {
                Ok(PlatformSpec::Platform(Arc::new(platform.to_platform()?)))
            }
            PlatformSpecSummary::Any => Ok(PlatformSpec::Any),
        }
    }

    /// Returns true if `self` is `PlatformSpecSummary::Any`.
    pub fn is_any(&self) -> bool {
        matches!(self, PlatformSpecSummary::Any)
    }
}

mod serde_impl {
    use super::*;
    use serde::{Deserialize, Deserializer, Serialize, Serializer};
    use std::collections::BTreeSet;
    use target_spec::summaries::TargetFeaturesSummary;

    impl Serialize for PlatformSpecSummary {
        fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
        where
            S: Serializer,
        {
            match self {
                PlatformSpecSummary::Always => Spec { spec: "always" }.serialize(serializer),
                PlatformSpecSummary::Any => Spec { spec: "any" }.serialize(serializer),
                PlatformSpecSummary::Platform(platform) => platform.serialize(serializer),
            }
        }
    }

    // Ideally we'd serialize always or any as just those strings, but that runs into ValueAfterTable
    // issues with toml. So serialize always/any as "spec = always" etc.
    #[derive(Serialize)]
    struct Spec {
        spec: &'static str,
    }

    impl<'de> Deserialize<'de> for PlatformSpecSummary {
        fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
        where
            D: Deserializer<'de>,
        {
            match PlatformSpecSummaryDeserialize::deserialize(deserializer)? {
                PlatformSpecSummaryDeserialize::String(spec)
                | PlatformSpecSummaryDeserialize::Spec { spec } => {
                    match spec.as_str() {
                        "always" => Ok(PlatformSpecSummary::Always),
                        "any" => Ok(PlatformSpecSummary::Any),
                        _ => {
                            // TODO: expression parsing would go here
                            Ok(PlatformSpecSummary::Platform(PlatformSummary::new(spec)))
                        }
                    }
                }
                PlatformSpecSummaryDeserialize::PlatformFull {
                    triple,
                    custom_json,
                    target_features,
                    flags,
                } => {
                    let mut summary = PlatformSummary::new(triple);
                    summary.custom_json = custom_json;
                    summary.target_features = target_features;
                    summary.flags = flags;
                    Ok(PlatformSpecSummary::Platform(summary))
                }
            }
        }
    }

    #[derive(Deserialize)]
    #[serde(untagged)]
    enum PlatformSpecSummaryDeserialize {
        String(String),
        Spec {
            spec: String,
        },
        #[serde(rename_all = "kebab-case")]
        PlatformFull {
            // TODO: there doesn't appear to be any way to defer to the PlatformSummary
            // deserializer, so copy-paste its logic here. Find a better way?
            triple: String,
            #[serde(skip_serializing_if = "Option::is_none", default)]
            custom_json: Option<String>,
            #[serde(default)]
            target_features: TargetFeaturesSummary,
            #[serde(skip_serializing_if = "BTreeSet::is_empty", default)]
            flags: BTreeSet<String>,
        },
    }
}

#[cfg(all(test, feature = "proptest1"))]
mod proptests {
    use super::*;
    use proptest::prelude::*;
    use std::collections::HashSet;

    proptest! {
        #[test]
        fn summary_roundtrip(platform_spec in any::<PlatformSpec>()) {
            let summary = PlatformSpecSummary::new(&platform_spec);
            let serialized = toml::ser::to_string(&summary).expect("serialization succeeded");

            let deserialized: PlatformSpecSummary = toml::from_str(&serialized).expect("deserialization succeeded");
            assert_eq!(summary, deserialized, "summary and deserialized should match");
            let platform_spec2 = deserialized.to_platform_spec().expect("conversion to PlatformSpec succeeded");

            match (platform_spec, platform_spec2) {
                (PlatformSpec::Any, PlatformSpec::Any)
                | (PlatformSpec::Always, PlatformSpec::Always) => {},
                (PlatformSpec::Platform(platform), PlatformSpec::Platform(platform2)) => {
                    assert_eq!(platform.triple_str(), platform2.triple_str(), "triples match");
                    assert_eq!(platform.target_features(), platform2.target_features(), "target features match");
                    assert_eq!(platform.flags().collect::<HashSet<_>>(), platform2.flags().collect::<HashSet<_>>(), "flags match");
                }
                (other, other2) => panic!("platform specs do not match: original: {other:?}, roundtrip: {other2:?}"),
            }
        }
    }
}
