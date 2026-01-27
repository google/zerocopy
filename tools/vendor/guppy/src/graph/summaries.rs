// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Generate build summaries from `CargoSet` instances.
//!
//! Requires the `summaries` feature to be enabled.

mod package_set;

use crate::{
    Error,
    graph::{
        DependencyDirection, PackageGraph, PackageMetadata, PackageSet, PackageSource,
        cargo::{CargoOptions, CargoResolverVersion, CargoSet, InitialsPlatform},
        feature::FeatureSet,
    },
    platform::PlatformSpecSummary,
};
pub use guppy_summaries::*;
pub use package_set::*;
use serde::{Deserialize, Serialize};
use std::collections::BTreeSet;

impl CargoSet<'_> {
    /// Creates a build summary with the given options.
    ///
    /// Requires the `summaries` feature to be enabled.
    pub fn to_summary(&self, opts: &CargoOptions<'_>) -> Result<Summary, Error> {
        let initials = self.initials();
        let metadata =
            CargoOptionsSummary::new(initials.graph().package_graph, self.features_only(), opts)?;
        let target_features = self.target_features();
        let host_features = self.host_features();

        let mut summary = Summary::with_metadata(&metadata).map_err(Error::TomlSerializeError)?;
        summary.target_packages =
            target_features.to_package_map(initials, self.target_direct_deps());
        summary.host_packages = host_features.to_package_map(initials, self.host_direct_deps());

        Ok(summary)
    }
}

impl<'g> FeatureSet<'g> {
    /// Creates a `PackageMap` from this `FeatureSet`.
    ///
    /// `initials` and `direct_deps` are used to assign a PackageStatus.
    fn to_package_map(
        &self,
        initials: &FeatureSet<'g>,
        direct_deps: &PackageSet<'g>,
    ) -> PackageMap {
        self.packages_with_features(DependencyDirection::Forward)
            .map(|feature_list| {
                let package = feature_list.package();

                let status = if initials.contains_package_ix(package.package_ix()) {
                    PackageStatus::Initial
                } else if package.in_workspace() {
                    PackageStatus::Workspace
                } else if direct_deps.contains_ix(package.package_ix()) {
                    PackageStatus::Direct
                } else {
                    PackageStatus::Transitive
                };

                let info = PackageInfo {
                    status,
                    features: feature_list
                        .named_features()
                        .map(|feature| feature.to_owned())
                        .collect(),
                    optional_deps: feature_list
                        .optional_deps()
                        .map(|dep| dep.to_owned())
                        .collect(),
                };

                (feature_list.package().to_summary_id(), info)
            })
            .collect()
    }
}

impl PackageGraph {
    /// Converts this `SummaryId` to a `PackageMetadata`.
    ///
    /// Returns an error if the summary ID could not be matched.
    ///
    /// Requires the `summaries` feature to be enabled.
    pub fn metadata_by_summary_id(
        &self,
        summary_id: &SummaryId,
    ) -> Result<PackageMetadata<'_>, Error> {
        match &summary_id.source {
            SummarySource::Workspace { workspace_path } => {
                self.workspace().member_by_path(workspace_path)
            }
            _ => {
                // Do a linear search for now -- this appears to be the easiest thing to do and is
                // pretty fast. This could potentially be sped up by building an index by name, but
                // at least for reasonably-sized graphs it's really fast.
                //
                // TODO: consider optimizing this in the future.
                let mut filter = self.packages().filter(|package| {
                    package.name() == summary_id.name
                        && package.version() == &summary_id.version
                        && package.source() == summary_id.source
                });
                filter
                    .next()
                    .ok_or_else(|| Error::UnknownSummaryId(summary_id.clone()))
            }
        }
    }
}

impl PackageMetadata<'_> {
    /// Converts this metadata to a `SummaryId`.
    ///
    /// Requires the `summaries` feature to be enabled.
    pub fn to_summary_id(&self) -> SummaryId {
        SummaryId {
            name: self.name().to_string(),
            version: self.version().clone(),
            source: self.source().to_summary_source(),
        }
    }
}

/// A summary of Cargo options used to build a `CargoSet`.
///
/// Requires the `summaries` feature to be enabled.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct CargoOptionsSummary {
    /// The Cargo resolver version used.
    ///
    /// For more information, see the documentation for [`CargoResolverVersion`].
    #[serde(alias = "version")]
    pub resolver: CargoResolverVersion,

    /// Whether dev-dependencies are included.
    pub include_dev: bool,

    /// The platform for which the initials are specified.
    #[serde(flatten)]
    pub initials_platform: InitialsPlatformSummary,

    /// The host platform.
    #[serde(default)]
    pub host_platform: PlatformSpecSummary,

    /// The target platform.
    #[serde(default)]
    pub target_platform: PlatformSpecSummary,

    /// The set of packages omitted from computations.
    #[serde(skip_serializing_if = "PackageSetSummary::is_empty", default)]
    pub omitted_packages: PackageSetSummary,

    /// The packages that formed the features-only set.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub features_only: Vec<FeaturesOnlySummary>,
}

impl CargoOptionsSummary {
    /// Creates a new `CargoOptionsSummary` from the given Cargo options.
    pub fn new(
        graph: &PackageGraph,
        features_only: &FeatureSet<'_>,
        opts: &CargoOptions<'_>,
    ) -> Result<Self, Error> {
        let omitted_packages =
            PackageSetSummary::from_package_ids(graph, opts.omitted_packages.iter().copied())?;

        let mut features_only = features_only
            .packages_with_features(DependencyDirection::Forward)
            .map(|features| FeaturesOnlySummary {
                summary_id: features.package().to_summary_id(),
                features: features
                    .named_features()
                    .map(|feature| feature.to_owned())
                    .collect(),
                optional_deps: features
                    .optional_deps()
                    .map(|feature| feature.to_owned())
                    .collect(),
            })
            .collect::<Vec<_>>();
        features_only.sort_unstable();

        Ok(Self {
            resolver: opts.resolver,
            include_dev: opts.include_dev,
            initials_platform: InitialsPlatformSummary::V2 {
                initials_platform: opts.initials_platform,
            },
            host_platform: PlatformSpecSummary::new(&opts.host_platform),
            target_platform: PlatformSpecSummary::new(&opts.target_platform),
            omitted_packages,
            features_only,
        })
    }

    /// Creates a new `CargoOptions` from this summary.
    pub fn to_cargo_options<'g>(
        &'g self,
        package_graph: &'g PackageGraph,
    ) -> Result<CargoOptions<'g>, Error> {
        let omitted_packages = self
            .omitted_packages
            .to_package_set(package_graph, "resolving omitted-packages")?;

        // TODO: return the features-only set

        let mut options = CargoOptions::new();
        options
            .set_resolver(self.resolver)
            .set_include_dev(self.include_dev)
            .set_initials_platform(self.initials_platform.into())
            .set_host_platform(
                self.host_platform.to_platform_spec().map_err(|err| {
                    Error::TargetSpecError("parsing host platform".to_string(), err)
                })?,
            )
            .set_target_platform(self.target_platform.to_platform_spec().map_err(|err| {
                Error::TargetSpecError("parsing target platform".to_string(), err)
            })?)
            .add_omitted_packages(omitted_packages.package_ids(DependencyDirection::Forward));
        Ok(options)
    }
}

/// Summary information for `InitialsPlatform`.
#[derive(Copy, Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(untagged, rename_all = "kebab-case")]
#[non_exhaustive]
pub enum InitialsPlatformSummary {
    /// The first version of this option, which only allowed setting `proc-macros-on-target`.
    #[serde(rename_all = "kebab-case")]
    V1 {
        /// If set to true, this is treated as `InitialsPlatform::ProcMacrosOnTarget`, otherwise as
        /// `InitialsPlatform::Standard`.
        proc_macros_on_target: bool,
    },
    /// The second and current version of this option.
    #[serde(rename_all = "kebab-case")]
    V2 {
        /// The configuration value.
        initials_platform: InitialsPlatform,
    },
}

impl From<InitialsPlatformSummary> for InitialsPlatform {
    fn from(s: InitialsPlatformSummary) -> Self {
        match s {
            InitialsPlatformSummary::V1 {
                proc_macros_on_target,
            } => {
                if proc_macros_on_target {
                    InitialsPlatform::ProcMacrosOnTarget
                } else {
                    InitialsPlatform::Standard
                }
            }
            InitialsPlatformSummary::V2 { initials_platform } => initials_platform,
        }
    }
}

/// Summary information for a features-only package.
///
/// These packages are stored in `CargoOptionsSummary` because they may or may not be in the final
/// build set.
#[derive(Clone, Debug, Deserialize, Eq, Ord, PartialEq, PartialOrd, Serialize)]
#[serde(rename_all = "kebab-case")]
#[non_exhaustive]
pub struct FeaturesOnlySummary {
    /// The summary ID for this feature.
    #[serde(flatten)]
    pub summary_id: SummaryId,

    /// The named features built for this package.
    pub features: BTreeSet<String>,

    /// The optional dependencies built for this package.
    #[serde(skip_serializing_if = "BTreeSet::is_empty", default)]
    pub optional_deps: BTreeSet<String>,
}

impl PackageSource<'_> {
    /// Converts a `PackageSource` into a `SummarySource`.
    ///
    /// Requires the `summaries` feature to be enabled.
    pub fn to_summary_source(&self) -> SummarySource {
        match self {
            PackageSource::Workspace(path) => SummarySource::workspace(path),
            PackageSource::Path(path) => SummarySource::path(path),
            PackageSource::External(source) => {
                if *source == PackageSource::CRATES_IO_REGISTRY {
                    SummarySource::crates_io()
                } else {
                    SummarySource::external(*source)
                }
            }
        }
    }
}

impl PartialEq<SummarySource> for PackageSource<'_> {
    fn eq(&self, summary_source: &SummarySource) -> bool {
        match summary_source {
            SummarySource::Workspace { workspace_path } => {
                self == &PackageSource::Workspace(workspace_path)
            }
            SummarySource::Path { path } => self == &PackageSource::Path(path),
            SummarySource::CratesIo => {
                self == &PackageSource::External(PackageSource::CRATES_IO_REGISTRY)
            }
            SummarySource::External { source } => self == &PackageSource::External(source),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_old_metadata() {
        // Ensure that previous versions of the metadata parse correctly.
        // TODO: note that there have been some compatibility breaks, particularly for
        // omitted-packages. Probably don't need to retain too much backwards compatibility.
        let metadata = "\
version = 'v1'
include-dev = true
proc-macros-on-target = false
";

        let summary: CargoOptionsSummary = toml::from_str(metadata).expect("parsed correctly");
        assert_eq!(
            InitialsPlatform::from(summary.initials_platform),
            InitialsPlatform::Standard
        );
    }
}
