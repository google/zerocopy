// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Contains types that describe errors and warnings that `guppy` methods can return.

use crate::{PackageId, graph::feature::FeatureId};
use Error::*;
use camino::Utf8PathBuf;
use std::{error, fmt};
pub use target_spec::Error as TargetSpecError;

/// Error type describing the sorts of errors `guppy` can return.
#[derive(Debug)]
#[non_exhaustive]
pub enum Error {
    /// An error occurred while executing `cargo metadata`.
    CommandError(Box<dyn error::Error + Send + Sync>),
    /// An error occurred while parsing `cargo metadata` JSON.
    MetadataParseError(serde_json::Error),
    /// An error occurred while serializing `cargo metadata` JSON.
    MetadataSerializeError(serde_json::Error),
    /// An error occurred while constructing a `PackageGraph` from parsed metadata.
    PackageGraphConstructError(String),
    /// A package ID was unknown to this `PackageGraph`.
    UnknownPackageId(PackageId),
    /// A feature ID was unknown to this `FeatureGraph`.
    UnknownFeatureId(PackageId, String),
    /// A package specified by path was unknown to this workspace.
    UnknownWorkspacePath(Utf8PathBuf),
    /// A package specified by name was unknown to this workspace.
    UnknownWorkspaceName(String),
    /// An error was returned by `target-spec`.
    TargetSpecError(String, TargetSpecError),
    /// An internal error occurred within this `PackageGraph`.
    PackageGraphInternalError(String),
    /// An internal error occurred within this `FeatureGraph`.
    FeatureGraphInternalError(String),
    /// A summary ID was unknown to this `PackageGraph`.
    ///
    /// This is present if the `summaries` feature is enabled.
    #[cfg(feature = "summaries")]
    UnknownSummaryId(guppy_summaries::SummaryId),
    /// While resolving a [`PackageSetSummary`](crate::graph::summaries::PackageSetSummary),
    /// some elements were unknown to the `PackageGraph`.
    ///
    /// This is present if the `summaries` feature is enabled.
    #[cfg(feature = "summaries")]
    UnknownPackageSetSummary {
        /// A description attached to the error.
        message: String,
        /// Summary IDs that weren't known to the `PackageGraph`.
        unknown_summary_ids: Vec<crate::graph::summaries::SummaryId>,
        /// Workspace packages that weren't known to the `PackageGraph`.
        unknown_workspace_members: Vec<String>,
        /// Third-party packages that weren't known to the `PackageGraph`.
        unknown_third_party: Vec<crate::graph::summaries::ThirdPartySummary>,
    },
    /// While resolving a [`PackageSetSummary`](crate::graph::summaries::PackageSetSummary),
    /// an unknown external registry was encountered.
    #[cfg(feature = "summaries")]
    UnknownRegistryName {
        /// A description attached to the error.
        message: String,

        /// The summary for which the name wasn't recognized.
        summary: Box<crate::graph::summaries::ThirdPartySummary>,

        /// The registry name that wasn't recognized.
        registry_name: String,
    },
    /// An error occurred while serializing to TOML.
    #[cfg(feature = "summaries")]
    TomlSerializeError(toml::ser::Error),
}

impl Error {
    pub(crate) fn command_error(err: cargo_metadata::Error) -> Self {
        Error::CommandError(Box::new(err))
    }

    pub(crate) fn unknown_feature_id(feature_id: FeatureId<'_>) -> Self {
        Error::UnknownFeatureId(
            feature_id.package_id().clone(),
            feature_id.label().to_string(),
        )
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommandError(_) => write!(f, "`cargo metadata` execution failed"),
            MetadataParseError(_) => write!(f, "`cargo metadata` returned invalid JSON output"),
            MetadataSerializeError(_) => write!(f, "failed to serialize `cargo metadata` to JSON"),
            PackageGraphConstructError(s) => write!(f, "failed to construct package graph: {s}"),
            UnknownPackageId(id) => write!(f, "unknown package ID: {id}"),
            UnknownFeatureId(package_id, feature) => {
                write!(f, "unknown feature ID: '{package_id}/{feature}'")
            }
            UnknownWorkspacePath(path) => write!(f, "unknown workspace path: {path}"),
            UnknownWorkspaceName(name) => write!(f, "unknown workspace package name: {name}"),
            TargetSpecError(msg, _) => write!(f, "target spec error while {msg}"),
            PackageGraphInternalError(msg) => write!(f, "internal error in package graph: {msg}"),
            FeatureGraphInternalError(msg) => write!(f, "internal error in feature graph: {msg}"),
            #[cfg(feature = "summaries")]
            UnknownSummaryId(summary_id) => write!(f, "unknown summary ID: {summary_id}"),
            #[cfg(feature = "summaries")]
            UnknownPackageSetSummary {
                message,
                unknown_summary_ids,
                unknown_workspace_members,
                unknown_third_party,
            } => {
                writeln!(f, "unknown elements: {message}")?;
                if !unknown_summary_ids.is_empty() {
                    writeln!(f, "* unknown summary IDs:")?;
                    for summary_id in unknown_summary_ids {
                        writeln!(f, "  - {summary_id}")?;
                    }
                }
                if !unknown_workspace_members.is_empty() {
                    writeln!(f, "* unknown workspace names:")?;
                    for workspace_member in unknown_workspace_members {
                        writeln!(f, "  - {workspace_member}")?;
                    }
                }
                if !unknown_third_party.is_empty() {
                    writeln!(f, "* unknown third-party:")?;
                    for third_party in unknown_third_party {
                        writeln!(f, "  - {third_party}")?;
                    }
                }
                Ok(())
            }
            #[cfg(feature = "summaries")]
            UnknownRegistryName {
                message,
                summary,
                registry_name,
            } => {
                writeln!(
                    f,
                    "unknown registry name: {message}\n* for third-party: {summary}\n* name: {registry_name}\n"
                )
            }
            #[cfg(feature = "summaries")]
            TomlSerializeError(_) => write!(f, "failed to serialize to TOML"),
        }
    }
}

impl error::Error for Error {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            MetadataParseError(err) => Some(err),
            MetadataSerializeError(err) => Some(err),
            CommandError(err) => Some(err.as_ref()),
            PackageGraphConstructError(_) => None,
            UnknownPackageId(_) => None,
            UnknownFeatureId(_, _) => None,
            UnknownWorkspacePath(_) => None,
            UnknownWorkspaceName(_) => None,
            TargetSpecError(_, err) => Some(err),
            PackageGraphInternalError(_) => None,
            FeatureGraphInternalError(_) => None,
            #[cfg(feature = "summaries")]
            UnknownSummaryId(_) => None,
            #[cfg(feature = "summaries")]
            UnknownPackageSetSummary { .. } => None,
            #[cfg(feature = "summaries")]
            UnknownRegistryName { .. } => None,
            #[cfg(feature = "summaries")]
            TomlSerializeError(err) => Some(err),
        }
    }
}

/// Describes warnings emitted during feature graph construction.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum FeatureGraphWarning {
    /// A feature that was requested is missing from a package.
    MissingFeature {
        /// The stage of building the feature graph where the warning occurred.
        stage: FeatureBuildStage,
        /// The package ID for which the feature was requested.
        package_id: PackageId,
        /// The name of the feature.
        feature_name: String,
    },

    /// A self-loop was discovered.
    SelfLoop {
        /// The package ID for which the self-loop was discovered.
        package_id: PackageId,
        /// The name of the feature for which the self-loop was discovered.
        feature_name: String,
    },
}

impl fmt::Display for FeatureGraphWarning {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use FeatureGraphWarning::*;
        match self {
            MissingFeature {
                stage,
                package_id,
                feature_name,
            } => write!(
                f,
                "{stage}: for package '{package_id}', missing feature '{feature_name}'"
            ),
            SelfLoop {
                package_id,
                feature_name,
            } => write!(
                f,
                "for package '{package_id}', self-loop detected for named feature '{feature_name}'"
            ),
        }
    }
}

/// Describes the stage of construction at which a feature graph warning occurred.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum FeatureBuildStage {
    /// The warning occurred while adding edges for the `[features]` section of `Cargo.toml`.
    AddNamedFeatureEdges {
        /// The package ID for which edges were being added.
        package_id: PackageId,
        /// The feature name from which edges were being added.
        from_feature: String,
    },
    /// The warning occurred while adding dependency edges.
    AddDependencyEdges {
        /// The package ID for which edges were being added.
        package_id: PackageId,
        /// The name of the dependency.
        dep_name: String,
    },
}

impl fmt::Display for FeatureBuildStage {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use FeatureBuildStage::*;
        match self {
            AddNamedFeatureEdges {
                package_id,
                from_feature,
            } => write!(
                f,
                "for package '{package_id}', while adding named feature edges from '{from_feature}'"
            ),
            AddDependencyEdges {
                package_id,
                dep_name,
            } => write!(
                f,
                "for package '{package_id}', while adding edges for dependency '{dep_name}'",
            ),
        }
    }
}
