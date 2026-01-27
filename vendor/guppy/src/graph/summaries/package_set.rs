// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    Error, PackageId,
    errors::Error::UnknownPackageSetSummary,
    graph::{
        DependencyDirection, ExternalSource, GitReq, PackageGraph, PackageMetadata, PackageSet,
        PackageSource,
    },
};
use ahash::AHashMap;
use camino::Utf8PathBuf;
use guppy_summaries::SummaryId;
use semver::VersionReq;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use smallvec::SmallVec;
use std::{borrow::Cow, collections::BTreeSet, fmt};

/// A set of packages specified in a summary. Can be resolved into a `PackageSet` given a
/// `PackageGraph`.
///
/// Requires the `summaries` feature to be enabled.
///
/// # Examples
///
/// Parsing a summary from a TOML specification, as found in e.g. a config file.
///
/// ```
/// # use guppy::graph::summaries::PackageSetSummary;
/// # use guppy::MetadataCommand;
/// # use guppy::graph::DependencyDirection;
/// # use std::collections::HashSet;
///
/// // This is an example TOML config for a PackageSet resolved from this workspace.
/// static TOML_INPUT: &str = r#"
/// workspace-members = ["guppy", "target-spec"]
/// ## The version field specifies a range, just like Cargo.
/// ## Third-party specifications also include "git" and "path".
/// third-party = [
///     { name = "serde", version = "*" },
///     { name = "rayon", version = "1.5" },
/// ]
/// "#;
///
/// let summary: PackageSetSummary = toml::from_str(TOML_INPUT).expect("input parsed correctly");
///
/// let graph = MetadataCommand::new().build_graph().expect("guppy graph constructed");
/// let package_set = summary
///     .to_package_set(&graph, "resolving example TOML")
///     .expect("all elements matched");
/// let package_names: HashSet<_> = package_set
///     .packages(DependencyDirection::Forward)
///     .map(|metadata| metadata.name())
///     .collect();
///
/// let mut expected_names = HashSet::new();
/// expected_names.extend(["guppy", "target-spec", "serde", "rayon"]);
/// assert_eq!(package_names, expected_names, "package names matched");
/// ```
///
/// Specifying an invalid package results in an error.
///
/// ```
/// # use guppy::graph::summaries::PackageSetSummary;
/// # use guppy::MetadataCommand;
///
/// // This is an example TOML config that contains package names that are unknown to this
/// // workspace.
/// static UNKNOWN_TOML_INPUT: &str = r#"
/// ## serde is a third-party dependency, so it won't be matched in workspace-members.
/// workspace-members = ["unknown-member", "serde"]
/// ## guppy is a workspace dependency, so it won't be matched in workspace-members.
/// ## serde is present but the version number doesn't match.
/// third-party = [
///     { name = "guppy" },
///     { name = "serde", version = "0.9" },
///     { name = "unknown-third-party" },
/// ]
/// "#;
///
/// let summary: PackageSetSummary = toml::from_str(UNKNOWN_TOML_INPUT).expect("input parsed correctly");
///
/// let graph = MetadataCommand::new().build_graph().expect("guppy graph constructed");
/// let err = summary
///     .to_package_set(&graph, "resolving example TOML")
///     .expect_err("some elements are unknown");
///
/// assert_eq!(
///     format!("{}", err),
///     r#"unknown elements: resolving example TOML
/// * unknown workspace names:
///   - serde
///   - unknown-member
/// * unknown third-party:
///   - { name = "guppy", version = "*", source = crates.io }
///   - { name = "serde", version = "^0.9", source = crates.io }
///   - { name = "unknown-third-party", version = "*", source = crates.io }
/// "#
/// );
/// ```
#[derive(Clone, Debug, Default, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
pub struct PackageSetSummary {
    /// A set of summary identifiers. Typically used in generated summaries.
    ///
    /// Does not require a `PackageGraph` as context.
    #[serde(rename = "ids", skip_serializing_if = "BTreeSet::is_empty", default)]
    pub summary_ids: BTreeSet<SummaryId>,

    /// Workspace packages, specified by names. Typically used in config files.
    ///
    /// These require a `PackageGraph` as context.
    #[serde(skip_serializing_if = "BTreeSet::is_empty", default)]
    pub workspace_members: BTreeSet<String>,

    // TODO: also support workspace path globs?
    // TODO: probably requires https://github.com/BurntSushi/ripgrep/issues/2001 to be fixed
    //
    /// Non-workspace packages, including non-workspace path dependencies. Typically used in
    /// config files.
    ///
    /// Requires a `PackageGraph` as context.
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub third_party: Vec<ThirdPartySummary>,
}

impl PackageSet<'_> {
    /// Converts this `PackageSet` to a serializable [`PackageSetSummary`].
    pub fn to_summary(&self) -> PackageSetSummary {
        PackageSetSummary::new(self)
    }
}

impl PackageSetSummary {
    /// Constructs a `PackageSetSummary` from a [`PackageSet`].
    pub fn new(package_set: &PackageSet<'_>) -> Self {
        let summary_ids = package_set
            .packages(DependencyDirection::Forward)
            .map(|metadata| metadata.to_summary_id())
            .collect();
        PackageSetSummary {
            summary_ids,
            ..PackageSetSummary::default()
        }
    }

    /// Constructs a `PackageSetSummary` from an iterator of [`PackageId`]s.
    pub fn from_package_ids<'a>(
        graph: &PackageGraph,
        package_ids: impl IntoIterator<Item = &'a PackageId>,
    ) -> Result<Self, Error> {
        let summary_ids = package_ids
            .into_iter()
            .map(|package_id| Ok(graph.metadata(package_id)?.to_summary_id()))
            .collect::<Result<_, Error>>()?;
        Ok(PackageSetSummary {
            summary_ids,
            ..PackageSetSummary::default()
        })
    }

    /// Returns true if this `PackageSetSummary` is empty.
    pub fn is_empty(&self) -> bool {
        self.summary_ids.is_empty()
            && self.workspace_members.is_empty()
            && self.third_party.is_empty()
    }

    /// Converts this `PackageSetSummary` to a [`PackageSet`].
    ///
    /// Returns an error if any of the elements weren't matched.
    pub fn to_package_set<'g>(
        &self,
        graph: &'g PackageGraph,
        error_message: impl Into<String>,
    ) -> Result<PackageSet<'g>, Error> {
        let error_message = error_message.into();
        let (package_set, matcher) = self.to_package_set_impl(graph, |_| None, &error_message)?;
        matcher.finish(graph, error_message)?;
        Ok(package_set)
    }

    /// Converts this `PackageSetSummary` to a [`PackageSet`], with the given source for registry
    /// names.
    ///
    /// Returns an error if any of the elements weren't matched.
    ///
    /// This is a temporary workaround until [Cargo issue #9052](https://github.com/rust-lang/cargo/issues/9052)
    /// is resolved.
    pub fn to_package_set_registry<'g, 'a>(
        &'a self,
        graph: &'g PackageGraph,
        registry_name_to_url: impl FnMut(&str) -> Option<&'a str>,
        error_message: impl Into<String>,
    ) -> Result<PackageSet<'g>, Error> {
        let error_message = error_message.into();
        let (package_set, matcher) =
            self.to_package_set_impl(graph, registry_name_to_url, &error_message)?;
        matcher.finish(graph, error_message)?;
        Ok(package_set)
    }

    // ---
    // Helper methods
    // ---

    fn to_package_set_impl<'g, 'a>(
        &'a self,
        graph: &'g PackageGraph,
        registry_name_to_url: impl FnMut(&str) -> Option<&'a str>,
        error_message: &str,
    ) -> Result<(PackageSet<'g>, PackageMatcher<'a>), Error> {
        let mut package_matcher = PackageMatcher::new(self, registry_name_to_url, error_message)?;
        let package_set = graph
            .resolve_all()
            .filter(DependencyDirection::Forward, |metadata| {
                package_matcher.store_is_match(metadata)
            });
        Ok((package_set, package_matcher))
    }
}

/// A selector for external, third-party packages.
///
/// A `ThirdPartySummary` is used to specify one or more packages based on the information
/// specified. Package names are required, but all other fields are optional.
///
/// Requires the `summaries` feature to be enabled.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ThirdPartySummary {
    /// The name of the package. Must be specified.
    pub name: String,

    /// A version specifier for the package. Can be skipped: defaults to [`VersionReq::STAR`].
    pub version: VersionReq,

    /// Where this package can be found. Can be skipped, in which case the source defaults to
    /// `crates.io`.
    pub source: ThirdPartySource,
}

impl fmt::Display for ThirdPartySummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{{ name = \"{}\", version = \"{}\", source = {} }}",
            self.name, self.version, self.source,
        )
    }
}

/// Describes locations where non-workspace packages (path or external) can be found.
///
/// This is a serializable form of part of [`PackageSource`], and is used by [`ThirdPartySummary`].
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum ThirdPartySource {
    /// A path dependency, relative to the workspace root.
    Path(Utf8PathBuf),

    /// A dependency on a registry. `crates.io` is represented as `None`.
    ///
    /// This should be the short name of the registry.
    Registry(Option<String>),

    /// A dependency on a Git repository.
    ///
    /// Contains the name of the Git repository, plus an optional branch, tag or revision
    /// identifier.
    Git {
        /// The repository path.
        repo: String,
        /// The Git branch, tag or revision, if specified.
        req: GitReqSummary,
    },

    /// A URL not otherwise recognized.
    Url(String),
}

impl fmt::Display for ThirdPartySource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ThirdPartySource::Path(path) => write!(f, "{{ path = {path} }}"),
            ThirdPartySource::Registry(Some(registry)) => {
                write!(f, "{{ registry = \"{registry}\" }}")
            }
            ThirdPartySource::Registry(None) => write!(f, "crates.io"),
            ThirdPartySource::Git { repo, req } => match req {
                GitReqSummary::Branch(branch) => {
                    write!(f, "{{ git = \"{repo}\", branch = \"{branch}\" }}")
                }
                GitReqSummary::Tag(tag) => {
                    write!(f, "{{ git = \"{repo}\", tag = \"{tag}\" }}")
                }
                GitReqSummary::Rev(rev) => {
                    write!(f, "{{ git = \"{repo}\", rev = \"{rev}\" }}")
                }
                GitReqSummary::Default => {
                    write!(f, "{{ git = \"{repo}\" }}")
                }
            },
            ThirdPartySource::Url(url) => write!(f, "{{ url = \"{url}\" }}"),
        }
    }
}

/// A summary specification for a Git branch, tag or revision.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub enum GitReqSummary {
    /// A branch, e.g. `"main"`.
    Branch(String),

    /// A tag, e.g. `"guppy-0.5.0"`.
    Tag(String),

    /// A revision (commit hash), e.g. `"0227f048fcb7c798026ede6cc20c92befc84c3a4"`.
    Rev(String),

    /// The main branch by default.
    Default,
}

impl GitReq<'_> {
    /// Converts `self` into a [`GitReqSummary`].
    ///
    /// Requires the `summaries` feature to be enabled.
    pub fn to_summary(self) -> GitReqSummary {
        GitReqSummary::new(self)
    }
}
impl GitReqSummary {
    /// Creates a new [`GitReqSummary`] from the provided [`GitReq`].
    pub fn new(git_req: GitReq<'_>) -> Self {
        match git_req {
            GitReq::Branch(branch) => GitReqSummary::Branch(branch.to_owned()),
            GitReq::Tag(tag) => GitReqSummary::Tag(tag.to_owned()),
            GitReq::Rev(rev) => GitReqSummary::Rev(rev.to_owned()),
            GitReq::Default => GitReqSummary::Default,
        }
    }

    /// Converts `self` into a [`GitReq`].
    pub fn as_git_req(&self) -> GitReq<'_> {
        match self {
            GitReqSummary::Branch(branch) => GitReq::Branch(branch.as_str()),
            GitReqSummary::Tag(tag) => GitReq::Tag(tag.as_str()),
            GitReqSummary::Rev(rev) => GitReq::Rev(rev.as_str()),
            GitReqSummary::Default => GitReq::Default,
        }
    }
}

// ---
// Serialization and deserialization
// ---

#[derive(Debug, Default, Deserialize, Serialize)]
struct ThirdPartySelectFields<'a> {
    #[serde(borrow)]
    name: Cow<'a, str>,
    #[serde(default, skip_serializing_if = "version_req_is_star")]
    version: VersionReq,

    // Fields that go into non-workspace source.
    #[serde(
        default,
        skip_serializing_if = "Option::is_none",
        serialize_with = "serialize_opt_path_fwdslash"
    )]
    path: Option<Utf8PathBuf>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[serde(borrow)]
    registry: Option<Cow<'a, str>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[serde(borrow)]
    git: Option<Cow<'a, str>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[serde(borrow)]
    branch: Option<Cow<'a, str>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[serde(borrow)]
    tag: Option<Cow<'a, str>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[serde(borrow)]
    rev: Option<Cow<'a, str>>,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    #[serde(borrow)]
    url: Option<Cow<'a, str>>,
}

impl<'de> Deserialize<'de> for ThirdPartySummary {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let fields = ThirdPartySelectFields::deserialize(deserializer)?;

        // Look for incompatible fields.
        let mut found_sources = vec![];
        if fields.path.is_some() {
            found_sources.push("`path`");
        }
        if fields.registry.is_some() {
            found_sources.push("`registry`");
        }
        if fields.git.is_some() {
            found_sources.push("`git`");
        }
        if fields.url.is_some() {
            found_sources.push("`url`");
        }

        let mut found_git = vec![];
        if fields.branch.is_some() {
            found_git.push("`branch`");
        }
        if fields.tag.is_some() {
            found_git.push("`tag`");
        }
        if fields.rev.is_some() {
            found_git.push("`rev`");
        }

        // Only one of the above fields can be present.
        if found_sources.len() > 1 {
            return Err(serde::de::Error::custom(format!(
                "for package {}, only one of {} can be present",
                fields.name,
                found_sources.join(", ")
            )));
        }

        let source = if let Some(path) = fields.path {
            if !found_git.is_empty() {
                return Err(serde::de::Error::custom(format!(
                    "for package {}, `path` incompatible with {}",
                    fields.name,
                    found_git.join(", ")
                )));
            }

            ThirdPartySource::Path(path)
        } else if let Some(git) = fields.git {
            if found_git.len() > 1 {
                return Err(serde::de::Error::custom(format!(
                    "for package {}, only one of {} can be present",
                    fields.name,
                    found_git.join(", ")
                )));
            }

            let req = if let Some(branch) = fields.branch {
                GitReqSummary::Branch(branch.into_owned())
            } else if let Some(tag) = fields.tag {
                GitReqSummary::Tag(tag.into_owned())
            } else if let Some(rev) = fields.rev {
                GitReqSummary::Rev(rev.into_owned())
            } else {
                GitReqSummary::Default
            };

            ThirdPartySource::Git {
                repo: git.into_owned(),
                req,
            }
        } else if let Some(url) = fields.url {
            if !found_git.is_empty() {
                return Err(serde::de::Error::custom(format!(
                    "for package {}, `url` incompatible with {}",
                    fields.name,
                    found_git.join(", ")
                )));
            }
            ThirdPartySource::Url(url.into_owned())
        } else {
            if !found_git.is_empty() {
                if fields.registry.is_some() {
                    return Err(serde::de::Error::custom(format!(
                        "for package {}, `registry` incompatible with {}",
                        fields.name,
                        found_git.join(", "),
                    )));
                } else {
                    return Err(serde::de::Error::custom(format!(
                        "for package {}, `git` required for {}",
                        fields.name,
                        found_git.join(", "),
                    )));
                }
            }
            ThirdPartySource::Registry(fields.registry.map(|registry| registry.into_owned()))
        };

        Ok(Self {
            name: fields.name.into_owned(),
            version: fields.version,
            source,
        })
    }
}

impl Serialize for ThirdPartySummary {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut fields = ThirdPartySelectFields {
            name: Cow::Borrowed(self.name.as_str()),
            version: self.version.clone(),
            ..ThirdPartySelectFields::default()
        };

        match &self.source {
            ThirdPartySource::Path(path) => {
                // Using clone rather than Cow::Borrowed here makes the deserialize impl simpler.
                fields.path = Some(path.clone());
            }
            ThirdPartySource::Url(url) => {
                fields.url = Some(Cow::Borrowed(url.as_str()));
            }
            ThirdPartySource::Registry(registry) => {
                fields.registry = registry.as_deref().map(Cow::Borrowed);
            }
            ThirdPartySource::Git { repo, req } => {
                fields.git = Some(Cow::Borrowed(repo.as_str()));
                match req {
                    GitReqSummary::Branch(branch) => {
                        fields.branch = Some(Cow::Borrowed(branch.as_str()))
                    }
                    GitReqSummary::Tag(tag) => fields.tag = Some(Cow::Borrowed(tag.as_str())),
                    GitReqSummary::Rev(rev) => fields.rev = Some(Cow::Borrowed(rev.as_str())),
                    GitReqSummary::Default => {}
                }
            }
        }

        fields.serialize(serializer)
    }
}

fn serialize_opt_path_fwdslash<S>(
    path: &Option<Utf8PathBuf>,
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: Serializer,
{
    match path {
        Some(path) => guppy_summaries::serialize_forward_slashes(path, serializer),
        None => serializer.serialize_none(),
    }
}

fn version_req_is_star(req: &VersionReq) -> bool {
    req == &VersionReq::STAR
}

// ---
// Package matching
// ---

#[derive(Debug)]
struct PackageMatcher<'a> {
    // The bools are to ensure that all the packages specified in the summary actually get matched
    // against something in the metadata.
    summary_ids: AHashMap<&'a SummaryId, bool>,
    workspace_members: &'a BTreeSet<String>,
    third_party: AHashMap<&'a str, SmallVec<[(&'a ThirdPartySummary, bool); 2]>>,
    registry_names_to_urls: AHashMap<&'a str, &'a str>,
}

impl<'a> PackageMatcher<'a> {
    fn new(
        summary: &'a PackageSetSummary,
        mut registry_name_to_url: impl FnMut(&str) -> Option<&'a str>,
        error_message: &str,
    ) -> Result<Self, Error> {
        let summary_ids = summary
            .summary_ids
            .iter()
            .map(|summary_id| (summary_id, false))
            .collect();

        let mut third_party: AHashMap<_, SmallVec<[_; 2]>> = AHashMap::new();
        let mut registry_names_to_urls = AHashMap::new();
        for tp_summary in &summary.third_party {
            if let ThirdPartySource::Registry(Some(name)) = &tp_summary.source {
                if !registry_names_to_urls.contains_key(name.as_str()) {
                    match registry_name_to_url(name) {
                        Some(url) => {
                            registry_names_to_urls.insert(name.as_str(), url);
                        }
                        None => {
                            return Err(Error::UnknownRegistryName {
                                message: error_message.to_owned(),
                                summary: Box::new(tp_summary.clone()),
                                registry_name: name.clone(),
                            });
                        }
                    }
                }
            }
            third_party
                .entry(tp_summary.name.as_str())
                .or_default()
                .push((tp_summary, false));
        }

        Ok(Self {
            summary_ids,
            workspace_members: &summary.workspace_members,
            third_party,
            registry_names_to_urls,
        })
    }

    /// Return whether something is a match, and record matches in `self`.
    fn store_is_match(&mut self, metadata: PackageMetadata<'_>) -> bool {
        // Don't short-circuit matches because we want to mark a
        // TODO: maybe this should involve duplicate detection between summary_ids and workspace/
        // third-party
        let name = metadata.name();
        let in_ids = match self.summary_ids.get_mut(&metadata.to_summary_id()) {
            Some(is_match_store) => {
                *is_match_store = true;
                true
            }
            None => false,
        };
        let in_selectors = if metadata.in_workspace() {
            self.workspace_members.contains(name)
        } else {
            let registry_names_to_urls = &self.registry_names_to_urls;
            match self.third_party.get_mut(name) {
                Some(matches) => {
                    let mut is_match = false;
                    for (summary, is_match_store) in matches {
                        if summary.version.matches(metadata.version())
                            && Self::source_matches(
                                metadata.source(),
                                &summary.source,
                                registry_names_to_urls,
                            )
                        {
                            // This is a match.
                            is_match = true;
                            *is_match_store = true;
                        }
                    }
                    is_match
                }
                None => false,
            }
        };

        in_ids || in_selectors
    }

    // Returns an error if any elements were unmatched.
    fn finish(self, graph: &PackageGraph, error_message: impl Into<String>) -> Result<(), Error> {
        let mut unknown_summary_ids: Vec<_> = self
            .summary_ids
            .into_iter()
            .filter_map(
                |(summary_id, matched)| {
                    if matched { None } else { Some(summary_id) }
                },
            )
            .cloned()
            .collect();
        unknown_summary_ids.sort_unstable();

        let workspace = graph.workspace();
        let unknown_workspace_members: Vec<_> = self
            .workspace_members
            .iter()
            .filter_map(|member| {
                if workspace.contains_name(member) {
                    None
                } else {
                    Some(member.clone())
                }
            })
            .collect();

        let mut unknown_third_party: Vec<_> =
            self.third_party
                .into_iter()
                .flat_map(|(_, summaries)| {
                    summaries.into_iter().filter_map(|(summary, matched)| {
                        if matched { None } else { Some(summary.clone()) }
                    })
                })
                .collect();
        unknown_third_party.sort_by(|x, y| x.name.cmp(&y.name));

        if unknown_summary_ids.is_empty()
            && unknown_workspace_members.is_empty()
            && unknown_third_party.is_empty()
        {
            Ok(())
        } else {
            Err(UnknownPackageSetSummary {
                message: error_message.into(),
                unknown_summary_ids,
                unknown_workspace_members,
                unknown_third_party,
            })
        }
    }

    // ---
    // Helper methods
    // ---

    fn source_matches(
        package_source: PackageSource<'_>,
        third_party_source: &ThirdPartySource,
        registry_names_to_urls: &AHashMap<&'a str, &'a str>,
    ) -> bool {
        match (package_source, third_party_source) {
            (PackageSource::Workspace(_), _) => {
                // third-party sources can't match a workspace package
                false
            }
            (PackageSource::Path(package_path), ThirdPartySource::Path(summary_path)) => {
                package_path == summary_path
            }
            (PackageSource::Path(_), _) => false,
            (PackageSource::External(external), ThirdPartySource::Url(summary_url)) => {
                external == summary_url
            }
            (external, _) => {
                let external_source = match external.parse_external() {
                    Some(external_source) => external_source,
                    None => {
                        // The only way this can match is with the ThirdPartySource::Url constraint
                        // above.
                        return false;
                    }
                };

                match (external_source, third_party_source) {
                    (
                        ExternalSource::Registry(external_registry_url),
                        ThirdPartySource::Registry(Some(summary_registry_name)),
                    ) => {
                        let &url = registry_names_to_urls
                            .get(summary_registry_name.as_str())
                            .expect("all names were already obtained in new()");
                        url == external_registry_url
                    }
                    (
                        ExternalSource::Registry(external_registry),
                        ThirdPartySource::Registry(None),
                    ) => external_registry == ExternalSource::CRATES_IO_URL,
                    (
                        ExternalSource::Git {
                            repository, req, ..
                        },
                        ThirdPartySource::Git {
                            repo: summary_repo,
                            req: summary_req,
                        },
                    ) => repository == summary_repo && summary_req.as_git_req() == req,
                    _ => false,
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::vec_init_then_push)]

    use super::*;
    use crate::graph::summaries::SummarySource;
    use semver::Version;

    #[test]
    fn valid() {
        let mut valids = vec![];
        valids.push(("", PackageSetSummary::default()));

        let mut summary_ids = BTreeSet::new();
        summary_ids.insert(SummaryId {
            name: "x".to_owned(),
            version: Version::parse("1.0.0").expect("version 1.0.0 parsed"),
            source: SummarySource::CratesIo,
        });
        valids.push((
            r#"[[ids]]
        name = "x"
        version = "1.0.0"
        crates-io = true
        "#,
            PackageSetSummary {
                summary_ids,
                ..PackageSetSummary::default()
            },
        ));

        valids.push((
            r#"#
            workspace-members = []"#,
            PackageSetSummary::default(),
        ));

        let mut workspace_members = BTreeSet::new();
        workspace_members.insert("abc".to_owned());
        valids.push((
            r#"
            workspace-members = ["abc"]"#,
            PackageSetSummary {
                workspace_members,
                ..PackageSetSummary::default()
            },
        ));

        let mut third_party = vec![];
        third_party.push(ThirdPartySummary {
            name: "foo".to_owned(),
            version: VersionReq::default(),
            source: ThirdPartySource::Registry(None),
        });

        valids.push((
            r#"
            third-party = [ { name = "foo" } ]"#,
            PackageSetSummary {
                third_party,
                ..PackageSetSummary::default()
            },
        ));

        let mut third_party = vec![];
        third_party.push(ThirdPartySummary {
            name: "foo".to_owned(),
            version: VersionReq::default(),
            source: ThirdPartySource::Git {
                repo: "git-repo".to_owned(),
                req: GitReqSummary::Default,
            },
        });
        third_party.push(ThirdPartySummary {
            name: "foo".to_owned(),
            version: VersionReq::parse(">2.0").expect("version >2.0 parsed correctly"),
            source: ThirdPartySource::Registry(Some("foo".to_owned())),
        });
        third_party.push(ThirdPartySummary {
            name: "bar".to_owned(),
            version: VersionReq::default(),
            source: ThirdPartySource::Git {
                repo: "git-repo".to_owned(),
                req: GitReqSummary::Branch("x".to_owned()),
            },
        });
        third_party.push(ThirdPartySummary {
            name: "bar".to_owned(),
            version: VersionReq::default(),
            source: ThirdPartySource::Git {
                repo: "git-repo".to_owned(),
                req: GitReqSummary::Tag("y".to_owned()),
            },
        });
        third_party.push(ThirdPartySummary {
            name: "baz".to_owned(),
            version: VersionReq::parse("4.1").expect("version 4.1 parsed correctly"),
            source: ThirdPartySource::Git {
                repo: "git-repo".to_owned(),
                req: GitReqSummary::Rev("z".to_owned()),
            },
        });
        third_party.push(ThirdPartySummary {
            name: "baz".to_owned(),
            version: VersionReq::default(),
            source: ThirdPartySource::Url("url".to_owned()),
        });
        valids.push((
            r#"
            third-party = [
                { name = "foo", git = "git-repo" },
                { name = "foo", registry = "foo", version = ">2.0" },
                { name = "bar", git = "git-repo", branch = "x" },
                { name = "bar", git = "git-repo", tag = "y" },
                { name = "baz", git = "git-repo", rev = "z", version = "4.1" },
                { name = "baz", version = "*", url = "url" },
        ]
        "#,
            PackageSetSummary {
                third_party,
                ..PackageSetSummary::default()
            },
        ));

        for (input, expected) in valids {
            let formatted_input = format_input(input);
            let actual = toml::de::from_str(input)
                .unwrap_or_else(|err| panic!("{formatted_input}\ndeserialization error: {err}"));
            assert_eq!(expected, actual, "{formatted_input}");

            let serialized = toml::ser::to_string(&actual)
                .unwrap_or_else(|err| panic!("{formatted_input}\nserialization error: {err}"));

            // Check that the serialized output matches by parsing it again.
            let actual2 = toml::de::from_str(&serialized).unwrap_or_else(|err| {
                panic!("{formatted_input}\ndeserialization error try 2: {err}")
            });
            assert_eq!(actual, actual2, "{formatted_input}");
        }
    }

    #[test]
    fn invalid() {
        let invalids = &[
            (
                r#"
                workspace-members = [ { name = "s" } ]"#,
                "expected a string for key `workspace-members`",
            ),
            (
                r#"third-party = [ { git = "git-repo" } ]"#,
                "missing field `name` for key `third-party`",
            ),
            (
                r#"
                third-party = [ { name = "x", path = "foo", git = "git-repo" } ]#",
                "#,
                "only one of `path`, `git` can be present",
            ),
            (
                r#"
                third-party = [ { name = "x", path = "foo", registry = "y" } ]
                "#,
                "only one of `path`, `registry` can be present",
            ),
            (
                r#"

                third-party = [ { name = "x", path = "foo", tag = "x" } ]
                "#,
                "`path` incompatible with `tag`",
            ),
            (
                r#"
                third-party = [ { name = "x", registry = "foo", rev = "z" } ]
                "#,
                "`registry` incompatible with `rev`",
            ),
            (
                r#"
                third-party = [ { name = "x", branch = "b" } ]
                "#,
                "`git` required for `branch`",
            ),
            (
                r#"
                third-party = [ { name = "x", git = "g", branch = "b", tag = "t" } ]
                "#,
                "only one of `branch`, `tag` can be present",
            ),
            (
                r#"
                third-party = [ { name = "x", git = "g", tag = "t", rev = "r" } ]
                "#,
                "only one of `tag`, `rev` can be present",
            ),
        ];

        for (input, err_msg) in invalids {
            let formatted_input = format_input(input);
            let err = match toml::de::from_str::<PackageSetSummary>(input) {
                Ok(output) => {
                    panic!("invalid input did not fail, {formatted_input}\noutput: {output:?}",)
                }
                Err(err) => err,
            };

            let err_display = format!("{err}");
            assert!(
                err_display.contains(err_msg),
                "{formatted_input}\nerror message '{err_display}' did not contain '{err_msg}"
            );
        }
    }

    fn format_input(input: &str) -> String {
        format!("input:\n---\n{input}\n---")
    }
}
