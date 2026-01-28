// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{Error, graph::PackageGraph};
use cargo_metadata::CargoOpt;
use serde::{Deserialize, Serialize};
use std::{convert::TryFrom, io, path::PathBuf, process::Command};

/// A builder for configuring `cargo metadata` invocations.
///
/// This is the most common entry point for constructing a `PackageGraph`.
///
/// ## Examples
///
/// Build a `PackageGraph` for the Cargo workspace in the current directory:
///
/// ```rust
/// use guppy::MetadataCommand;
/// use guppy::graph::PackageGraph;
///
/// let mut cmd = MetadataCommand::new();
/// let package_graph = PackageGraph::from_command(&mut cmd);
/// ```
#[derive(Clone, Debug, Default)]
pub struct MetadataCommand {
    inner: cargo_metadata::MetadataCommand,
}

impl MetadataCommand {
    /// Creates a default `cargo metadata` command builder.
    ///
    /// By default, this will look for `Cargo.toml` in the ancestors of this process's current
    /// directory.
    pub fn new() -> Self {
        let mut inner = cargo_metadata::MetadataCommand::new();
        // Always use --all-features so that we get a full view of the graph.
        inner.features(CargoOpt::AllFeatures);
        Self { inner }
    }

    /// Sets the path to the `cargo` executable.
    ///
    /// If unset, this will use the `$CARGO` environment variable, or else `cargo` from `$PATH`.
    pub fn cargo_path(&mut self, path: impl Into<PathBuf>) -> &mut Self {
        self.inner.cargo_path(path);
        self
    }

    /// Sets the path to `Cargo.toml`.
    ///
    /// By default, this will look for `Cargo.toml` in the ancestors of the current directory. Note
    /// that this doesn't need to be the root `Cargo.toml` in a workspace -- any member of the
    /// workspace is fine.
    pub fn manifest_path(&mut self, path: impl Into<PathBuf>) -> &mut Self {
        self.inner.manifest_path(path);
        self
    }

    /// Sets the current directory of the `cargo metadata` process.
    ///
    /// By default, the current directory will be inherited from this process.
    pub fn current_dir(&mut self, path: impl Into<PathBuf>) -> &mut Self {
        self.inner.current_dir(path);
        self
    }

    /// Output information only about the workspace and do not fetch dependencies.
    ///
    /// For full functionality, `cargo metadata` should be run without `--no-deps`, so that `guppy`
    /// knows about third-party crates and dependency edges. However, `guppy` supports a "light"
    /// mode if `--no-deps` is run, in which case the following limitations will apply:
    /// * dependency queries will not work
    /// * there will be no information about non-workspace crates
    ///
    /// Constructing a graph with this option can be several times faster than the default.
    pub fn no_deps(&mut self) -> &mut Self {
        self.inner.no_deps();
        self
    }

    // *Do not* implement features.

    /// Arbitrary flags to pass to `cargo metadata`. These will be added to the end of the
    /// command invocation.
    ///
    /// Note that `guppy` internally:
    /// * uses `--format-version 1` as its metadata format.
    /// * passes in `--all-features`, so that `guppy` has a full view of the dependency graph.
    ///
    /// Attempting to override either of those options may lead to unexpected results.
    pub fn other_options(
        &mut self,
        options: impl IntoIterator<Item = impl Into<String>>,
    ) -> &mut Self {
        self.inner
            .other_options(options.into_iter().map(|s| s.into()).collect::<Vec<_>>());
        self
    }

    /// Arbitrary environment variables to set when running cargo. These will be merged into the
    /// calling environment, overriding any which clash.
    pub fn env(
        &mut self,
        key: impl Into<std::ffi::OsString>,
        val: impl Into<std::ffi::OsString>,
    ) -> &mut Self {
        self.inner.env(key, val);
        self
    }

    /// Builds a [`Command`] instance. This is the first part of calling
    /// [`exec`](Self::exec).
    pub fn cargo_command(&self) -> Command {
        self.inner.cargo_command()
    }

    /// Runs the configured `cargo metadata` and returns a deserialized `CargoMetadata`.
    pub fn exec(&self) -> Result<CargoMetadata, Error> {
        let inner = self.inner.exec().map_err(Error::command_error)?;
        Ok(CargoMetadata(inner))
    }

    /// Runs the configured `cargo metadata` and returns a parsed `PackageGraph`.
    pub fn build_graph(&self) -> Result<PackageGraph, Error> {
        let metadata = self.exec()?;
        metadata.build_graph()
    }
}

/// Although consuming a `MetadataCommand` is not required for building a `PackageGraph`, this impl
/// is provided for convenience.
impl TryFrom<MetadataCommand> for PackageGraph {
    type Error = Error;

    fn try_from(command: MetadataCommand) -> Result<Self, Self::Error> {
        command.build_graph()
    }
}

impl<'a> TryFrom<&'a MetadataCommand> for PackageGraph {
    type Error = Error;

    fn try_from(command: &'a MetadataCommand) -> Result<Self, Self::Error> {
        command.build_graph()
    }
}

/// Deserialized Cargo metadata.
///
/// Returned by a `MetadataCommand` or constructed from `cargo metadata` JSON output.
///
/// This is an alternative entry point for constructing a `PackageGraph`, to be used if the JSON
/// output of `cargo metadata` is already available. To construct a `PackageGraph` from an on-disk
/// Cargo workspace, use [`MetadataCommand`](MetadataCommand).
///
/// This struct implements `serde::Serialize` and `Deserialize`.
#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(transparent)]
pub struct CargoMetadata(pub(crate) cargo_metadata::Metadata);

impl CargoMetadata {
    /// Deserializes this JSON blob into a `CargoMetadata`.
    pub fn parse_json(json: impl AsRef<str>) -> Result<Self, Error> {
        let inner = serde_json::from_str(json.as_ref()).map_err(Error::MetadataParseError)?;
        Ok(Self(inner))
    }

    /// Serializes this metadata into the given writer.
    pub fn serialize(&self, writer: &mut impl io::Write) -> Result<(), Error> {
        serde_json::to_writer(writer, &self.0).map_err(Error::MetadataSerializeError)
    }

    /// Parses this metadata and builds a `PackageGraph` from it.
    pub fn build_graph(self) -> Result<PackageGraph, Error> {
        PackageGraph::from_metadata(self)
    }
}

impl TryFrom<CargoMetadata> for PackageGraph {
    type Error = Error;

    fn try_from(metadata: CargoMetadata) -> Result<Self, Self::Error> {
        metadata.build_graph()
    }
}
