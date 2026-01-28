// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    CargoMetadata, DependencyKind, Error, JsonValue, MetadataCommand, PackageId,
    graph::{
        BuildTarget, BuildTargetId, BuildTargetImpl, BuildTargetKind, Cycles, DependencyDirection,
        OwnedBuildTargetId, PackageIx, PackageQuery, PackageSet, cargo_version_matches,
        feature::{FeatureGraphImpl, FeatureId, FeatureLabel, FeatureNode},
    },
    petgraph_support::{IxBitSet, scc::Sccs, topo::TopoWithCycles},
    platform::{EnabledTernary, PlatformSpec, PlatformStatus, PlatformStatusImpl},
};
use ahash::AHashMap;
use camino::{Utf8Path, Utf8PathBuf};
use fixedbitset::FixedBitSet;
use indexmap::{IndexMap, IndexSet};
use once_cell::sync::OnceCell;
use petgraph::{
    algo::{DfsSpace, has_path_connecting},
    graph::EdgeReference,
    prelude::*,
    visit::EdgeFiltered,
};
use semver::{Version, VersionReq};
use smallvec::SmallVec;
use std::{
    collections::{BTreeMap, HashSet},
    fmt,
    iter::{self, FromIterator},
};

use super::feature::{FeatureFilter, FeatureSet};

/// A graph of packages and dependencies between them, parsed from metadata returned by `cargo
/// metadata`.
///
/// For examples on how to use `PackageGraph`, see
/// [the `examples` directory](https://github.com/guppy-rs/guppy/tree/main/guppy/examples)
/// in this crate.
#[derive(Clone, Debug)]
pub struct PackageGraph {
    // Source of truth data.
    pub(super) dep_graph: Graph<PackageId, PackageLinkImpl, Directed, PackageIx>,
    // The strongly connected components of the graph, computed on demand.
    pub(super) sccs: OnceCell<Sccs<PackageIx>>,
    // Feature graph, computed on demand.
    pub(super) feature_graph: OnceCell<FeatureGraphImpl>,
    // XXX Should this be in an Arc for quick cloning? Not clear how this would work with node
    // filters though.
    pub(super) data: PackageGraphData,
}

/// Per-package data for a PackageGraph instance.
#[derive(Clone, Debug)]
pub(super) struct PackageGraphData {
    pub(super) packages: AHashMap<PackageId, PackageMetadataImpl>,
    pub(super) workspace: WorkspaceImpl,
}

impl PackageGraph {
    /// Executes the given `MetadataCommand` and constructs a `PackageGraph` from it.
    pub fn from_command(command: &mut MetadataCommand) -> Result<Self, Error> {
        command.build_graph()
    }

    /// Parses the given `Metadata` and constructs a `PackageGraph` from it.
    pub fn from_metadata(metadata: CargoMetadata) -> Result<Self, Error> {
        Self::build(metadata.0).map_err(|error| *error)
    }

    /// Constructs a package graph from the given JSON output of `cargo metadata`.
    ///
    /// Generally, `guppy` expects the `cargo metadata` command to be run with `--all-features`, so
    /// that `guppy` has a full view of the dependency graph.
    ///
    /// For full functionality, `cargo metadata` should be run without `--no-deps`, so that `guppy`
    /// knows about third-party crates and dependency edges. However, `guppy` supports a "light"
    /// mode if `--no-deps` is run, in which case the following limitations will apply:
    /// * dependency queries will not work
    /// * there will be no information about non-workspace crates
    pub fn from_json(json: impl AsRef<str>) -> Result<Self, Error> {
        let metadata = CargoMetadata::parse_json(json)?;
        Self::from_metadata(metadata)
    }

    /// Verifies internal invariants on this graph. Not part of the documented API.
    #[doc(hidden)]
    pub fn verify(&self) -> Result<(), Error> {
        // Graph structure checks.
        let node_count = self.dep_graph.node_count();
        let package_count = self.data.packages.len();
        if node_count != package_count {
            return Err(Error::PackageGraphInternalError(format!(
                "number of nodes = {node_count} different from packages = {package_count}",
            )));
        }

        // TODO: The dependency graph can have cyclic dev-dependencies. Add a check to ensure that
        // the graph without any dev-only dependencies is acyclic.

        let workspace = self.workspace();
        let workspace_ids: HashSet<_> = workspace.member_ids().collect();

        for metadata in self.packages() {
            let package_id = metadata.id();

            match metadata.source().workspace_path() {
                Some(workspace_path) => {
                    // This package is in the workspace, so the workspace should have information
                    // about it.
                    let metadata2 = workspace.member_by_path(workspace_path);
                    let metadata2_id = metadata2.map(|metadata| metadata.id());
                    if !matches!(metadata2_id, Ok(id) if id == package_id) {
                        return Err(Error::PackageGraphInternalError(format!(
                            "package {package_id} has workspace path {workspace_path:?} but query by path returned {metadata2_id:?}",
                        )));
                    }

                    let metadata3 = workspace.member_by_name(metadata.name());
                    let metadata3_id = metadata3.map(|metadata| metadata.id());
                    if !matches!(metadata3_id, Ok(id) if id == package_id) {
                        return Err(Error::PackageGraphInternalError(format!(
                            "package {} has name {}, but workspace query by name returned {:?}",
                            package_id,
                            metadata.name(),
                            metadata3_id,
                        )));
                    }
                }
                None => {
                    // This package is not in the workspace.
                    if workspace_ids.contains(package_id) {
                        return Err(Error::PackageGraphInternalError(format!(
                            "package {package_id} has no workspace path but is in workspace",
                        )));
                    }
                }
            }

            for build_target in metadata.build_targets() {
                match build_target.id() {
                    BuildTargetId::Library | BuildTargetId::BuildScript => {
                        // Ensure that the name is populated (this may panic if it isn't).
                        build_target.name();
                    }
                    BuildTargetId::Binary(name)
                    | BuildTargetId::Example(name)
                    | BuildTargetId::Test(name)
                    | BuildTargetId::Benchmark(name) => {
                        if name != build_target.name() {
                            return Err(Error::PackageGraphInternalError(format!(
                                "package {} has build target name mismatch ({} != {})",
                                package_id,
                                name,
                                build_target.name(),
                            )));
                        }
                    }
                }

                let id_kind_mismatch = match build_target.id() {
                    BuildTargetId::Library => match build_target.kind() {
                        BuildTargetKind::LibraryOrExample(_) | BuildTargetKind::ProcMacro => false,
                        BuildTargetKind::Binary => true,
                    },
                    BuildTargetId::Example(_) => match build_target.kind() {
                        BuildTargetKind::LibraryOrExample(_) => false,
                        BuildTargetKind::ProcMacro | BuildTargetKind::Binary => true,
                    },
                    BuildTargetId::BuildScript
                    | BuildTargetId::Binary(_)
                    | BuildTargetId::Test(_)
                    | BuildTargetId::Benchmark(_) => match build_target.kind() {
                        BuildTargetKind::LibraryOrExample(_) | BuildTargetKind::ProcMacro => true,
                        BuildTargetKind::Binary => false,
                    },
                };

                if id_kind_mismatch {
                    return Err(Error::PackageGraphInternalError(format!(
                        "package {} has build target id {:?}, which doesn't match kind {:?}",
                        package_id,
                        build_target.id(),
                        build_target.kind(),
                    )));
                }
            }

            for link in self.dep_links_ixs_directed(metadata.package_ix(), Outgoing) {
                let to = link.to();
                let to_id = to.id();
                let to_version = to.version();

                // Two invariants:
                // 1. At least one of the edges should be specified.
                // 2. The specified package should match the version dependency.

                let req = link.version_req();
                // A requirement of "*" filters out pre-release versions with the semver crate,
                // but cargo accepts them.
                // See https://github.com/steveklabnik/semver/issues/98.
                if !cargo_version_matches(req, to_version) {
                    return Err(Error::PackageGraphInternalError(format!(
                        "{package_id} -> {to_id}: version ({to_version}) doesn't match requirement ({req:?})",
                    )));
                }

                let is_any = link.normal().is_present()
                    || link.build().is_present()
                    || link.dev().is_present();

                if !is_any {
                    return Err(Error::PackageGraphInternalError(format!(
                        "{package_id} -> {to_id}: no edge info found",
                    )));
                }
            }
        }

        // Construct and check the feature graph for internal consistency.
        self.feature_graph().verify()?;

        Ok(())
    }

    /// Returns information about the workspace.
    pub fn workspace(&self) -> Workspace<'_> {
        Workspace {
            graph: self,
            inner: &self.data.workspace,
        }
    }

    /// Returns an iterator over all the package IDs in this graph.
    pub fn package_ids(&self) -> impl ExactSizeIterator<Item = &PackageId> {
        self.data.package_ids()
    }

    /// Returns an iterator over all the packages in this graph.
    pub fn packages(&self) -> impl ExactSizeIterator<Item = PackageMetadata<'_>> {
        self.data
            .packages
            .values()
            .map(move |inner| PackageMetadata::new(self, inner))
    }

    /// Returns the metadata for the given package ID.
    pub fn metadata(&self, package_id: &PackageId) -> Result<PackageMetadata<'_>, Error> {
        let inner = self
            .data
            .metadata_impl(package_id)
            .ok_or_else(|| Error::UnknownPackageId(package_id.clone()))?;
        Ok(PackageMetadata::new(self, inner))
    }

    /// Returns the number of packages in this graph.
    pub fn package_count(&self) -> usize {
        // This can be obtained in two different ways: self.dep_graph.node_count() or
        // self.data.packages.len(). verify() checks that they return the same results.
        //
        // Use this way for symmetry with link_count below (which can only be obtained through the
        // graph).
        self.dep_graph.node_count()
    }

    /// Returns the number of links in this graph.
    pub fn link_count(&self) -> usize {
        self.dep_graph.edge_count()
    }

    /// Creates a new cache for `depends_on` queries.
    ///
    /// The cache is optional but can speed up some queries.
    pub fn new_depends_cache(&self) -> DependsCache<'_> {
        DependsCache::new(self)
    }

    /// Returns true if `package_a` depends (directly or indirectly) on `package_b`.
    ///
    /// In other words, this returns true if `package_b` is a (possibly transitive) dependency of
    /// `package_a`.
    ///
    /// This also returns true if `package_a` is the same as `package_b`.
    ///
    /// For repeated queries, consider using `new_depends_cache` to speed up queries.
    pub fn depends_on(&self, package_a: &PackageId, package_b: &PackageId) -> Result<bool, Error> {
        let mut depends_cache = self.new_depends_cache();
        depends_cache.depends_on(package_a, package_b)
    }

    /// Returns true if `package_a` directly depends on `package_b`.
    ///
    /// In other words, this returns true if `package_b` is a direct dependency of `package_a`.
    ///
    /// This returns false if `package_a` is the same as `package_b`.
    pub fn directly_depends_on(
        &self,
        package_a: &PackageId,
        package_b: &PackageId,
    ) -> Result<bool, Error> {
        let a_ix = self.package_ix(package_a)?;
        let b_ix = self.package_ix(package_b)?;
        Ok(self.dep_graph.contains_edge(a_ix, b_ix))
    }

    /// Returns information about dependency cycles in this graph.
    ///
    /// For more information, see the documentation for `Cycles`.
    pub fn cycles(&self) -> Cycles<'_> {
        Cycles::new(self)
    }

    // For more traversals, see query.rs.

    // ---
    // Helper methods
    // ---

    fn dep_links_ixs_directed(
        &self,
        package_ix: NodeIndex<PackageIx>,
        dir: Direction,
    ) -> impl Iterator<Item = PackageLink<'_>> {
        self.dep_graph
            .edges_directed(package_ix, dir)
            .map(move |edge| self.edge_ref_to_link(edge))
    }

    fn link_between_ixs(
        &self,
        from_ix: NodeIndex<PackageIx>,
        to_ix: NodeIndex<PackageIx>,
    ) -> Option<PackageLink<'_>> {
        self.dep_graph
            .find_edge(from_ix, to_ix)
            .map(|edge_ix| self.edge_ix_to_link(edge_ix))
    }

    /// Constructs a map of strongly connected components for this graph.
    pub(super) fn sccs(&self) -> &Sccs<PackageIx> {
        self.sccs.get_or_init(|| {
            let edge_filtered =
                EdgeFiltered::from_fn(&self.dep_graph, |edge| !edge.weight().dev_only());
            // Sort the entire graph without dev-only edges -- a correct graph would be cycle-free
            // but we don't currently do a consistency check for this so handle cycles.
            // TODO: should we check at construction time? or bubble up a warning somehow?
            let topo = TopoWithCycles::new(&edge_filtered);

            Sccs::new(&self.dep_graph, |scc| {
                topo.sort_nodes(scc);
            })
        })
    }

    /// Invalidates internal caches. Primarily for testing.
    #[doc(hidden)]
    pub fn invalidate_caches(&mut self) {
        self.sccs.take();
        self.feature_graph.take();
    }

    /// Returns the inner dependency graph.
    ///
    /// Should this be exposed publicly? Not sure.
    pub(super) fn dep_graph(&self) -> &Graph<PackageId, PackageLinkImpl, Directed, PackageIx> {
        &self.dep_graph
    }

    /// Maps an edge reference to a dependency link.
    pub(super) fn edge_ref_to_link<'g>(
        &'g self,
        edge: EdgeReference<'g, PackageLinkImpl, PackageIx>,
    ) -> PackageLink<'g> {
        PackageLink::new(
            self,
            edge.source(),
            edge.target(),
            edge.id(),
            Some(edge.weight()),
        )
    }

    /// Maps an edge index to a dependency link.
    pub(super) fn edge_ix_to_link(&self, edge_ix: EdgeIndex<PackageIx>) -> PackageLink<'_> {
        let (source_ix, target_ix) = self
            .dep_graph
            .edge_endpoints(edge_ix)
            .expect("valid edge ix");
        PackageLink::new(
            self,
            source_ix,
            target_ix,
            edge_ix,
            self.dep_graph.edge_weight(edge_ix),
        )
    }

    /// Maps an iterator of package IDs to their internal graph node indexes.
    pub(super) fn package_ixs<'g, 'a, B>(
        &'g self,
        package_ids: impl IntoIterator<Item = &'a PackageId>,
    ) -> Result<B, Error>
    where
        B: iter::FromIterator<NodeIndex<PackageIx>>,
    {
        package_ids
            .into_iter()
            .map(|package_id| self.package_ix(package_id))
            .collect()
    }

    /// Maps a package ID to its internal graph node index, and returns an `UnknownPackageId` error
    /// if the package isn't found.
    pub(super) fn package_ix(&self, package_id: &PackageId) -> Result<NodeIndex<PackageIx>, Error> {
        Ok(self.metadata(package_id)?.package_ix())
    }
}

impl PackageGraphData {
    /// Returns an iterator over all the package IDs in this graph.
    pub fn package_ids(&self) -> impl ExactSizeIterator<Item = &PackageId> {
        self.packages.keys()
    }

    // ---
    // Helper methods
    // ---

    #[inline]
    pub(super) fn metadata_impl(&self, package_id: &PackageId) -> Option<&PackageMetadataImpl> {
        self.packages.get(package_id)
    }
}

/// An optional cache used to speed up `depends_on` queries.
///
/// Created with `PackageGraph::new_depends_cache()`.
#[derive(Clone, Debug)]
pub struct DependsCache<'g> {
    package_graph: &'g PackageGraph,
    dfs_space: DfsSpace<NodeIndex<PackageIx>, FixedBitSet>,
}

impl<'g> DependsCache<'g> {
    /// Creates a new cache for `depends_on` queries for this package graph.
    ///
    /// This holds a shared reference to the package graph. This is to ensure that the cache is
    /// invalidated if the package graph is mutated.
    pub fn new(package_graph: &'g PackageGraph) -> Self {
        Self {
            package_graph,
            dfs_space: DfsSpace::new(&package_graph.dep_graph),
        }
    }

    /// Returns true if `package_a` depends (directly or indirectly) on `package_b`.
    ///
    /// In other words, this returns true if `package_b` is a (possibly transitive) dependency of
    /// `package_a`.
    pub fn depends_on(
        &mut self,
        package_a: &PackageId,
        package_b: &PackageId,
    ) -> Result<bool, Error> {
        let a_ix = self.package_graph.package_ix(package_a)?;
        let b_ix = self.package_graph.package_ix(package_b)?;
        Ok(has_path_connecting(
            self.package_graph.dep_graph(),
            a_ix,
            b_ix,
            Some(&mut self.dfs_space),
        ))
    }
}

/// Information about a workspace, parsed from metadata returned by `cargo metadata`.
///
/// For more about workspaces, see
/// [Cargo Workspaces](https://doc.rust-lang.org/book/ch14-03-cargo-workspaces.html) in *The Rust
/// Programming Language*.
#[derive(Clone, Debug)]
pub struct Workspace<'g> {
    graph: &'g PackageGraph,
    pub(super) inner: &'g WorkspaceImpl,
}

impl<'g> Workspace<'g> {
    /// Returns the workspace root.
    pub fn root(&self) -> &'g Utf8Path {
        &self.inner.root
    }

    /// Returns the target directory in which output artifacts are stored.
    pub fn target_directory(&self) -> &'g Utf8Path {
        &self.inner.target_directory
    }

    /// Returns the build directory in which intermediate build artifacts are
    /// stored.
    ///
    /// This field is only available if the `Metadata` was generated by Cargo
    /// 1.91 or later.
    pub fn build_directory(&self) -> Option<&'g Utf8Path> {
        self.inner.build_directory.as_deref()
    }

    /// Returns an iterator over the workspace default members.
    ///
    /// Default members are the packages that are built when `cargo build` is
    /// run without any arguments in the workspace root.
    ///
    /// This field is only available if the `Metadata` was generated by Cargo
    /// 1.71 or later. For older versions, this will return an empty iterator.
    pub fn default_member_ids(&self) -> impl ExactSizeIterator<Item = &'g PackageId> + use<'g> {
        self.inner.default_members.iter()
    }

    /// Returns an iterator over package metadatas for workspace default
    /// members.
    ///
    /// Default members are the packages that are built when `cargo build` is
    /// run without any arguments in the workspace root.
    ///
    /// This field is only available if the `Metadata` was generated by Cargo
    /// 1.71 or later. For older versions, this will return an empty iterator.
    pub fn default_members(&self) -> impl ExactSizeIterator<Item = PackageMetadata<'g>> + use<'g> {
        let graph = self.graph;
        self.inner
            .default_members
            .iter()
            .map(move |id| graph.metadata(id).expect("valid package ID"))
    }

    /// Returns the number of packages in this workspace.
    pub fn member_count(&self) -> usize {
        self.inner.members_by_path.len()
    }

    /// Returns true if the workspace contains a package by the given name.
    pub fn contains_name(&self, name: impl AsRef<str>) -> bool {
        self.inner.members_by_name.contains_key(name.as_ref())
    }

    /// Returns true if the workspace contains a package by the given workspace path.
    pub fn contains_path(&self, path: impl AsRef<Utf8Path>) -> bool {
        self.inner.members_by_path.contains_key(path.as_ref())
    }

    /// Returns an iterator over package metadatas, sorted by the path they're in.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = PackageMetadata<'g>> + use<'g> {
        self.iter_by_path().map(|(_, package)| package)
    }

    /// Returns an iterator over workspace paths and package metadatas, sorted by the path
    /// they're in.
    pub fn iter_by_path(
        &self,
    ) -> impl ExactSizeIterator<Item = (&'g Utf8Path, PackageMetadata<'g>)> + use<'g> {
        let graph = self.graph;
        self.inner.members_by_path.iter().map(move |(path, id)| {
            (
                path.as_path(),
                graph.metadata(id).expect("valid package ID"),
            )
        })
    }

    /// Returns an iterator over workspace names and package metadatas, sorted by names.
    pub fn iter_by_name(
        &self,
    ) -> impl ExactSizeIterator<Item = (&'g str, PackageMetadata<'g>)> + use<'g> {
        let graph = self.graph;
        self.inner
            .members_by_name
            .iter()
            .map(move |(name, id)| (name.as_ref(), graph.metadata(id).expect("valid package ID")))
    }

    /// Returns an iterator over package IDs for workspace members. The package IDs will be returned
    /// in the same order as `members`, sorted by the path they're in.
    pub fn member_ids(&self) -> impl ExactSizeIterator<Item = &'g PackageId> + use<'g> {
        self.inner.members_by_path.values()
    }

    /// Maps the given path to the corresponding workspace member.
    ///
    /// Returns an error if the path didn't match any workspace members.
    pub fn member_by_path(&self, path: impl AsRef<Utf8Path>) -> Result<PackageMetadata<'g>, Error> {
        let path = path.as_ref();
        let id = self
            .inner
            .members_by_path
            .get(path)
            .ok_or_else(|| Error::UnknownWorkspacePath(path.to_path_buf()))?;
        Ok(self.graph.metadata(id).expect("valid package ID"))
    }

    /// Maps the given paths to their corresponding workspace members, returning a new value of
    /// the specified collection type (e.g. `Vec`).
    ///
    /// Returns an error if any of the paths were unknown.
    pub fn members_by_paths<B>(
        &self,
        paths: impl IntoIterator<Item = impl AsRef<Utf8Path>>,
    ) -> Result<B, Error>
    where
        B: FromIterator<PackageMetadata<'g>>,
    {
        paths
            .into_iter()
            .map(|path| self.member_by_path(path.as_ref()))
            .collect()
    }

    /// Maps the given name to the corresponding workspace member.
    ///
    /// Returns an error if the name didn't match any workspace members.
    pub fn member_by_name(&self, name: impl AsRef<str>) -> Result<PackageMetadata<'g>, Error> {
        let name = name.as_ref();
        let id = self
            .inner
            .members_by_name
            .get(name)
            .ok_or_else(|| Error::UnknownWorkspaceName(name.to_string()))?;
        Ok(self.graph.metadata(id).expect("valid package ID"))
    }

    /// Maps the given names to their corresponding workspace members, returning a new value of
    /// the specified collection type (e.g. `Vec`).
    ///
    /// Returns an error if any of the paths were unknown.
    pub fn members_by_names<B>(
        &self,
        names: impl IntoIterator<Item = impl AsRef<str>>,
    ) -> Result<B, Error>
    where
        B: FromIterator<PackageMetadata<'g>>,
    {
        names
            .into_iter()
            .map(|name| self.member_by_name(name.as_ref()))
            .collect()
    }

    /// Returns the freeform metadata table for this workspace.
    ///
    /// This is the same as the `workspace.metadata` section of `Cargo.toml`. This section is
    /// typically used by tools which would like to store workspace configuration in `Cargo.toml`.
    pub fn metadata_table(&self) -> &'g JsonValue {
        &self.inner.metadata_table
    }
}

#[cfg(feature = "rayon1")]
mod workspace_rayon {
    use super::*;
    use rayon::prelude::*;

    /// These parallel iterators require the `rayon1` feature is enabled.
    impl<'g> Workspace<'g> {
        /// Returns a parallel iterator over package metadatas, sorted by workspace path.
        ///
        /// Requires the `rayon1` feature to be enabled.
        pub fn par_iter(&self) -> impl ParallelIterator<Item = PackageMetadata<'g>> + use<'g> {
            self.par_iter_by_path().map(|(_, package)| package)
        }

        /// Returns a parallel iterator over workspace paths and package metadatas, sorted by
        /// workspace paths.
        ///
        /// Requires the `rayon1` feature to be enabled.
        pub fn par_iter_by_path(
            &self,
        ) -> impl ParallelIterator<Item = (&'g Utf8Path, PackageMetadata<'g>)> + use<'g> {
            let graph = self.graph;
            self.inner
                .members_by_path
                .par_iter()
                .map(move |(path, id)| {
                    (
                        path.as_path(),
                        graph.metadata(id).expect("valid package ID"),
                    )
                })
        }

        /// Returns a parallel iterator over workspace names and package metadatas, sorted by
        /// package names.
        ///
        /// Requires the `rayon1` feature to be enabled.
        pub fn par_iter_by_name(
            &self,
        ) -> impl ParallelIterator<Item = (&'g str, PackageMetadata<'g>)> + use<'g> {
            let graph = self.graph;
            self.inner
                .members_by_name
                .par_iter()
                .map(move |(name, id)| {
                    (name.as_ref(), graph.metadata(id).expect("valid package ID"))
                })
        }
    }
}

#[derive(Clone, Debug)]
pub(super) struct WorkspaceImpl {
    pub(super) root: Utf8PathBuf,
    pub(super) target_directory: Utf8PathBuf,
    pub(super) build_directory: Option<Utf8PathBuf>,
    pub(super) metadata_table: JsonValue,
    // This is a BTreeMap to allow presenting data in sorted order.
    pub(super) members_by_path: BTreeMap<Utf8PathBuf, PackageId>,
    pub(super) members_by_name: BTreeMap<Box<str>, PackageId>,
    pub(super) default_members: Vec<PackageId>,
    // Cache for members by name (only used for proptests)
    #[cfg(feature = "proptest1")]
    pub(super) name_list: OnceCell<Vec<Box<str>>>,
}

/// Information about a specific package in a `PackageGraph`.
///
/// Most of the metadata is extracted from `Cargo.toml` files. See
/// [the `Cargo.toml` reference](https://doc.rust-lang.org/cargo/reference/manifest.html) for more
/// details.
#[derive(Copy, Clone)]
pub struct PackageMetadata<'g> {
    graph: &'g PackageGraph,
    inner: &'g PackageMetadataImpl,
}

impl fmt::Debug for PackageMetadata<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("PackageMetadata")
            .field("package_id", &self.id().repr())
            .field("..", &"..")
            .finish()
    }
}

assert_covariant!(PackageMetadata);

impl<'g> PackageMetadata<'g> {
    pub(super) fn new(graph: &'g PackageGraph, inner: &'g PackageMetadataImpl) -> Self {
        Self { graph, inner }
    }

    /// Returns the unique identifier for this package.
    pub fn id(&self) -> &'g PackageId {
        &self.graph.dep_graph[self.inner.package_ix]
    }

    /// Returns the package graph this `PackageMetadata` is derived from.
    pub fn graph(&self) -> &'g PackageGraph {
        self.graph
    }

    /// Creates a `PackageQuery` consisting of this package, in the given direction.
    ///
    /// The `PackageQuery` can be used to inspect dependencies in this graph.
    pub fn to_package_query(&self, direction: DependencyDirection) -> PackageQuery<'g> {
        self.graph
            .query_from_parts(iter::once(self.inner.package_ix).collect(), direction)
    }

    /// Creates a `PackageSet` consisting of just this package.
    pub fn to_package_set(&self) -> PackageSet<'g> {
        let included: IxBitSet = iter::once(self.package_ix()).collect();
        PackageSet::from_included(self.graph, included)
    }

    /// Creates a `FeatureSet` that consists of all features in the package that match the given
    /// named filter.
    pub fn to_feature_set(&self, features: impl FeatureFilter<'g>) -> FeatureSet<'g> {
        self.to_package_set().to_feature_set(features)
    }

    // ---
    // Dependency traversals
    // ---

    /// Returns `PackageLink` instances corresponding to the direct dependencies for this package in
    /// the specified direction.
    pub fn direct_links_directed(
        &self,
        direction: DependencyDirection,
    ) -> impl Iterator<Item = PackageLink<'g>> + 'g + use<'g> {
        self.direct_links_impl(direction.into())
    }

    /// Returns `PackageLink` instances corresponding to the direct dependencies for this package.
    pub fn direct_links(&self) -> impl Iterator<Item = PackageLink<'g>> + 'g + use<'g> {
        self.direct_links_impl(Outgoing)
    }

    /// Returns `PackageLink` instances corresponding to the packages that directly depend on this
    /// one.
    pub fn reverse_direct_links(&self) -> impl Iterator<Item = PackageLink<'g>> + 'g + use<'g> {
        self.direct_links_impl(Incoming)
    }

    /// Returns the direct `PackageLink` between `self` and `other` in the specified direction:
    /// * `Forward`: from `self` to `other`
    /// * `Reverse`: from `other` to `self`
    ///
    /// Returns `None` if the direct link does not exist, or an error if `to` isn't found in
    /// `self.graph()`.
    pub fn link_between(
        &self,
        other: &PackageId,
        direction: DependencyDirection,
    ) -> Result<Option<PackageLink<'g>>, Error> {
        self.link_between_impl(other, direction.into())
    }

    /// Returns the direct `PackageLink` from `self` to the specified package, or `None` if `self`
    /// does not directly depend on the specified package.
    ///
    /// Returns an error if `to` isn't found in `self.graph()`.
    pub fn link_to(&self, to: &PackageId) -> Result<Option<PackageLink<'g>>, Error> {
        self.link_between_impl(to, Outgoing)
    }

    /// Returns the direct `PackageLink` from the specified package to `self`, or `None` if the
    /// specified package does not directly depend on `self`.
    ///
    /// Returns an error if `from` isn't found in `self.graph()`.
    pub fn link_from(&self, from: &PackageId) -> Result<Option<PackageLink<'g>>, Error> {
        self.link_between_impl(from, Incoming)
    }

    // ---
    // Package fields
    // ---

    /// Returns the name of this package.
    ///
    /// This is the same as the `name` field of `Cargo.toml`.
    pub fn name(&self) -> &'g str {
        &self.inner.name
    }

    /// Returns the version of this package as resolved by Cargo.
    ///
    /// This is the same as the `version` field of `Cargo.toml`.
    pub fn version(&self) -> &'g Version {
        &self.inner.version
    }

    /// Returns the authors of this package.
    ///
    /// This is the same as the `authors` field of `Cargo.toml`.
    pub fn authors(&self) -> &'g [String] {
        &self.inner.authors
    }

    /// Returns a short description for this package.
    ///
    /// This is the same as the `description` field of `Cargo.toml`.
    pub fn description(&self) -> Option<&'g str> {
        self.inner.description.as_ref().map(|x| x.as_ref())
    }

    /// Returns an SPDX 2.1 license expression for this package, if specified.
    ///
    /// This is the same as the `license` field of `Cargo.toml`. Note that `guppy` does not perform
    /// any validation on this, though `crates.io` does if a crate is uploaded there.
    pub fn license(&self) -> Option<&'g str> {
        self.inner.license.as_ref().map(|x| x.as_ref())
    }

    /// Returns the path to a license file for this package, if specified.
    ///
    /// This is the same as the `license_file` field of `Cargo.toml`. It is typically only specified
    /// for nonstandard licenses.
    pub fn license_file(&self) -> Option<&'g Utf8Path> {
        self.inner.license_file.as_ref().map(|path| path.as_ref())
    }

    /// Returns the source from which this package was retrieved.
    ///
    /// This may be the workspace path, an external path, or a registry like `crates.io`.
    pub fn source(&self) -> PackageSource<'g> {
        PackageSource::new(&self.inner.source)
    }

    /// Returns true if this package is in the workspace.
    ///
    /// For more detailed information, use `source()`.
    pub fn in_workspace(&self) -> bool {
        self.source().is_workspace()
    }

    /// Returns the full path to the `Cargo.toml` for this package.
    ///
    /// This is specific to the system that `cargo metadata` was run on.
    pub fn manifest_path(&self) -> &'g Utf8Path {
        &self.inner.manifest_path
    }

    /// Returns categories for this package.
    ///
    /// This is the same as the `categories` field of `Cargo.toml`. For packages on `crates.io`,
    /// returned values are guaranteed to be
    /// [valid category slugs](https://crates.io/category_slugs).
    pub fn categories(&self) -> &'g [String] {
        &self.inner.categories
    }

    /// Returns keywords for this package.
    ///
    /// This is the same as the `keywords` field of `Cargo.toml`.
    pub fn keywords(&self) -> &'g [String] {
        &self.inner.keywords
    }

    /// Returns a path to the README for this package, if specified.
    ///
    /// This is the same as the `readme` field of `Cargo.toml`. The path returned is relative to the
    /// directory the `Cargo.toml` is in (i.e. relative to the parent of `self.manifest_path()`).
    pub fn readme(&self) -> Option<&'g Utf8Path> {
        self.inner.readme.as_ref().map(|path| path.as_ref())
    }

    /// Returns the source code repository for this package, if specified.
    ///
    /// This is the same as the `repository` field of `Cargo.toml`.
    pub fn repository(&self) -> Option<&'g str> {
        self.inner.repository.as_ref().map(|x| x.as_ref())
    }

    /// Returns the homepage for this package, if specified.
    ///
    /// This is the same as the `homepage` field of `Cargo.toml`.
    pub fn homepage(&self) -> Option<&'g str> {
        self.inner.homepage.as_ref().map(|x| x.as_ref())
    }

    /// Returns the documentation URL for this package, if specified.
    ///
    /// This is the same as the `homepage` field of `Cargo.toml`.
    pub fn documentation(&self) -> Option<&'g str> {
        self.inner.documentation.as_ref().map(|x| x.as_ref())
    }

    /// Returns the Rust edition this package is written against.
    ///
    /// This is the same as the `edition` field of `Cargo.toml`. It is `"2015"` by default.
    pub fn edition(&self) -> &'g str {
        &self.inner.edition
    }

    /// Returns the freeform metadata table for this package.
    ///
    /// This is the same as the `package.metadata` section of `Cargo.toml`. This section is
    /// typically used by tools which would like to store package configuration in `Cargo.toml`.
    pub fn metadata_table(&self) -> &'g JsonValue {
        &self.inner.metadata_table
    }

    /// Returns the name of a native library this package links to, if specified.
    ///
    /// This is the same as the `links` field of `Cargo.toml`. See [The `links` Manifest
    /// Key](https://doc.rust-lang.org/cargo/reference/build-scripts.html#the-links-manifest-key) in
    /// the Cargo book for more details.
    pub fn links(&self) -> Option<&'g str> {
        self.inner.links.as_ref().map(|x| x.as_ref())
    }

    /// Returns the registries to which this package may be published.
    ///
    /// This is derived from the `publish` field of `Cargo.toml`.
    pub fn publish(&self) -> PackagePublish<'g> {
        PackagePublish::new(&self.inner.publish)
    }

    /// Returns the binary that is run by default, if specified.
    ///
    /// Information about this binary can be queried using [the `build_target`
    /// method](Self::build_target).
    ///
    /// This is derived from the `default-run` field of `Cargo.toml`.
    pub fn default_run(&self) -> Option<&'g str> {
        self.inner.default_run.as_ref().map(|x| x.as_ref())
    }

    /// Returns the minimum Rust compiler version, which should be able to compile the package, if
    /// specified.
    ///
    /// This is the same as the `rust-version` field of `Cargo.toml`. For more, see [the
    /// `rust-version` field](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field)
    /// in the Cargo reference.
    pub fn minimum_rust_version(&self) -> Option<&'g Version> {
        self.inner.rust_version.as_ref()
    }

    /// Returns the minimum Rust compiler version, which should be able to compile the package, if
    /// specified.
    ///
    /// Returned as a [`semver::VersionReq`]. This is actually not correct -- it is deprecated and
    /// will go away in the next major version of guppy: use [`Self::minimum_rust_version`] instead.
    ///
    /// This is the same as the `rust-version` field of `Cargo.toml`. For more, see [the
    /// `rust-version`
    /// field](https://doc.rust-lang.org/cargo/reference/manifest.html#the-rust-version-field) in
    /// the Cargo reference.
    #[deprecated(
        since = "0.17.1",
        note = "use Self::rust_version instead, it returns a Version"
    )]
    pub fn rust_version(&self) -> Option<&'g VersionReq> {
        self.inner.rust_version_req.as_ref()
    }

    /// Returns all the build targets for this package.
    ///
    /// For more, see [Cargo
    /// Targets](https://doc.rust-lang.org/nightly/cargo/reference/cargo-targets.html#cargo-targets)
    /// in the Cargo reference.
    pub fn build_targets(&self) -> impl Iterator<Item = BuildTarget<'g>> + use<'g> {
        self.inner.build_targets.iter().map(BuildTarget::new)
    }

    /// Looks up a build target by identifier.
    pub fn build_target(&self, id: &BuildTargetId<'_>) -> Option<BuildTarget<'g>> {
        self.inner
            .build_targets
            .get_key_value(id.as_key())
            .map(BuildTarget::new)
    }

    /// Returns true if this package is a procedural macro.
    ///
    /// For more about procedural macros, see [Procedural
    /// Macros](https://doc.rust-lang.org/reference/procedural-macros.html) in the Rust reference.
    pub fn is_proc_macro(&self) -> bool {
        match self.build_target(&BuildTargetId::Library) {
            Some(build_target) => matches!(build_target.kind(), BuildTargetKind::ProcMacro),
            None => false,
        }
    }

    /// Returns true if this package has a build script.
    ///
    /// Cargo only follows build dependencies if a build script is set.
    ///
    /// For more about build scripts, see [Build
    /// Scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html) in the Cargo
    /// reference.
    pub fn has_build_script(&self) -> bool {
        self.build_target(&BuildTargetId::BuildScript).is_some()
    }

    /// Returns true if this package has a named feature named `default`.
    ///
    /// For more about default features, see [The `[features]`
    /// section](https://doc.rust-lang.org/cargo/reference/manifest.html#the-features-section) in
    /// the Cargo reference.
    pub fn has_default_feature(&self) -> bool {
        self.inner.has_default_feature
    }

    /// Returns the `FeatureId` corresponding to the default feature.
    pub fn default_feature_id(&self) -> FeatureId<'g> {
        if self.inner.has_default_feature {
            FeatureId::new(self.id(), FeatureLabel::Named("default"))
        } else {
            FeatureId::base(self.id())
        }
    }

    /// Returns the list of named features available for this package. This will include a feature
    /// named "default" if it is defined.
    ///
    /// A named feature is listed in the `[features]` section of `Cargo.toml`. For more, see
    /// [the reference](https://doc.rust-lang.org/cargo/reference/manifest.html#the-features-section).
    pub fn named_features(&self) -> impl Iterator<Item = &'g str> + 'g + use<'g> {
        self.named_features_full()
            .map(|(_, named_feature, _)| named_feature)
    }

    // ---
    // Helper methods
    // --

    #[inline]
    pub(super) fn package_ix(&self) -> NodeIndex<PackageIx> {
        self.inner.package_ix
    }

    fn link_between_impl(
        &self,
        other: &PackageId,
        dir: Direction,
    ) -> Result<Option<PackageLink<'g>>, Error> {
        let other_ix = self.graph.package_ix(other)?;
        match dir {
            Direction::Outgoing => Ok(self.graph.link_between_ixs(self.package_ix(), other_ix)),
            Direction::Incoming => Ok(self.graph.link_between_ixs(other_ix, self.package_ix())),
        }
    }

    fn direct_links_impl(
        &self,
        dir: Direction,
    ) -> impl Iterator<Item = PackageLink<'g>> + 'g + use<'g> {
        self.graph.dep_links_ixs_directed(self.package_ix(), dir)
    }

    pub(super) fn get_feature_idx(&self, label: FeatureLabel<'_>) -> Option<FeatureIndexInPackage> {
        match label {
            FeatureLabel::Base => Some(FeatureIndexInPackage::Base),
            FeatureLabel::OptionalDependency(dep_name) => self
                .inner
                .optional_deps
                .get_index_of(dep_name)
                .map(FeatureIndexInPackage::OptionalDependency),
            FeatureLabel::Named(feature_name) => self
                .inner
                .named_features
                .get_index_of(feature_name)
                .map(FeatureIndexInPackage::Named),
        }
    }

    pub(super) fn feature_idx_to_label(&self, idx: FeatureIndexInPackage) -> FeatureLabel<'g> {
        match idx {
            FeatureIndexInPackage::Base => FeatureLabel::Base,
            FeatureIndexInPackage::OptionalDependency(idx) => FeatureLabel::OptionalDependency(
                self.inner
                    .optional_deps
                    .get_index(idx)
                    .expect("feature idx in optional_deps should be valid")
                    .as_ref(),
            ),
            FeatureIndexInPackage::Named(idx) => FeatureLabel::Named(
                self.inner
                    .named_features
                    .get_index(idx)
                    .expect("feature idx in optional_deps should be valid")
                    .0
                    .as_ref(),
            ),
        }
    }

    #[allow(dead_code)]
    pub(super) fn all_feature_nodes(&self) -> impl Iterator<Item = FeatureNode> + 'g + use<'g> {
        let package_ix = self.package_ix();
        iter::once(FeatureNode::new(
            self.package_ix(),
            FeatureIndexInPackage::Base,
        ))
        .chain(
            (0..self.inner.named_features.len())
                .map(move |named_idx| FeatureNode::named_feature(package_ix, named_idx)),
        )
        .chain(
            (0..self.inner.optional_deps.len())
                .map(move |dep_idx| FeatureNode::optional_dep(package_ix, dep_idx)),
        )
    }

    pub(super) fn named_features_full(
        &self,
    ) -> impl Iterator<Item = (FeatureIndexInPackage, &'g str, &'g [NamedFeatureDep])> + 'g + use<'g>
    {
        self.inner
            .named_features
            .iter()
            // IndexMap is documented to use indexes 0..n without holes, so this enumerate()
            // is correct.
            .enumerate()
            .map(|(idx, (feature, deps))| {
                (
                    FeatureIndexInPackage::Named(idx),
                    feature.as_ref(),
                    deps.as_slice(),
                )
            })
    }

    pub(super) fn optional_deps_full(
        &self,
    ) -> impl Iterator<Item = (FeatureIndexInPackage, &'g str)> + 'g + use<'g> {
        self.inner
            .optional_deps
            .iter()
            // IndexMap is documented to use indexes 0..n without holes, so this enumerate()
            // is correct.
            .enumerate()
            .map(|(idx, dep_name)| {
                (
                    FeatureIndexInPackage::OptionalDependency(idx),
                    dep_name.as_ref(),
                )
            })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum FeatureIndexInPackage {
    Base,
    OptionalDependency(usize),
    Named(usize),
}

/// `PackageMetadata`'s `PartialEq` implementation uses pointer equality for the `PackageGraph`.
impl PartialEq for PackageMetadata<'_> {
    fn eq(&self, other: &Self) -> bool {
        // Checking for the same package ix is enough as each package is guaranteed to be a 1:1 map
        // with ixs.
        std::ptr::eq(self.graph, other.graph) && self.package_ix() == other.package_ix()
    }
}

impl Eq for PackageMetadata<'_> {}

#[derive(Clone, Debug)]
pub(crate) struct PackageMetadataImpl {
    // Implementation note: we use Box<str> and Box<Path> to save on memory use when possible.

    // Fields extracted from the package.
    pub(super) name: Box<str>,
    pub(super) version: Version,
    pub(super) authors: Vec<String>,
    pub(super) description: Option<Box<str>>,
    pub(super) license: Option<Box<str>>,
    pub(super) license_file: Option<Box<Utf8Path>>,
    pub(super) manifest_path: Box<Utf8Path>,
    pub(super) categories: Vec<String>,
    pub(super) keywords: Vec<String>,
    pub(super) readme: Option<Box<Utf8Path>>,
    pub(super) repository: Option<Box<str>>,
    pub(super) homepage: Option<Box<str>>,
    pub(super) documentation: Option<Box<str>>,
    pub(super) edition: Box<str>,
    pub(super) metadata_table: JsonValue,
    pub(super) links: Option<Box<str>>,
    pub(super) publish: PackagePublishImpl,
    pub(super) default_run: Option<Box<str>>,
    pub(super) rust_version: Option<Version>,
    pub(super) rust_version_req: Option<VersionReq>,
    pub(super) named_features: IndexMap<Box<str>, SmallVec<[NamedFeatureDep; 4]>>,
    pub(super) optional_deps: IndexSet<Box<str>>,

    // Other information.
    pub(super) package_ix: NodeIndex<PackageIx>,
    pub(super) source: PackageSourceImpl,
    pub(super) build_targets: BTreeMap<OwnedBuildTargetId, BuildTargetImpl>,
    pub(super) has_default_feature: bool,
}

/// The source of a package.
///
/// This enum contains information about where a package is found, and whether it is inside or
/// outside the workspace.
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
pub enum PackageSource<'g> {
    /// This package is in the workspace.
    ///
    /// The path is relative to the workspace root.
    Workspace(&'g Utf8Path),

    /// This package is a path dependency that isn't in the workspace.
    ///
    /// The path is relative to the workspace root.
    Path(&'g Utf8Path),

    /// This package is an external dependency.
    ///
    /// * For packages retrieved from `crates.io`, the source is the string
    ///   `"registry+https://github.com/rust-lang/crates.io-index"`.
    /// * For packages retrieved from other registries, the source begins with `"registry+"`.
    /// * For packages retrieved from Git repositories, the source begins with `"git+"`.
    External(&'g str),
}

assert_covariant!(PackageSource);

impl<'g> PackageSource<'g> {
    /// The path to the crates.io registry.
    pub const CRATES_IO_REGISTRY: &'static str =
        "registry+https://github.com/rust-lang/crates.io-index";

    pub(super) fn new(inner: &'g PackageSourceImpl) -> Self {
        match inner {
            PackageSourceImpl::Workspace(path) => PackageSource::Workspace(path),
            PackageSourceImpl::Path(path) => PackageSource::Path(path),
            PackageSourceImpl::CratesIo => PackageSource::External(Self::CRATES_IO_REGISTRY),
            PackageSourceImpl::External(source) => PackageSource::External(source),
        }
    }

    /// Returns true if this package source represents a workspace.
    pub fn is_workspace(&self) -> bool {
        matches!(self, PackageSource::Workspace(_))
    }

    /// Returns true if this package source represents a path dependency that isn't in the
    /// workspace.
    pub fn is_path(&self) -> bool {
        matches!(self, PackageSource::Path(_))
    }

    /// Returns true if this package source represents an external dependency.
    pub fn is_external(&self) -> bool {
        matches!(self, PackageSource::External(_))
    }

    /// Returns true if the source is `crates.io`.
    pub fn is_crates_io(&self) -> bool {
        matches!(self, PackageSource::External(Self::CRATES_IO_REGISTRY))
    }

    /// Returns true if this package is a local dependency, i.e. either in the workspace or a local
    /// path.
    pub fn is_local(&self) -> bool {
        !self.is_external()
    }

    /// Returns the path if this is a workspace dependency, or `None` if this is a non-workspace
    /// dependency.
    ///
    /// The path is relative to the workspace root.
    pub fn workspace_path(&self) -> Option<&'g Utf8Path> {
        match self {
            PackageSource::Workspace(path) => Some(path),
            _ => None,
        }
    }

    /// Returns the local path if this is a local dependency, or `None` if it is an external
    /// dependency.
    ///
    /// The path is relative to the workspace root.
    pub fn local_path(&self) -> Option<&'g Utf8Path> {
        match self {
            PackageSource::Path(path) | PackageSource::Workspace(path) => Some(path),
            _ => None,
        }
    }

    /// Returns the external source if this is an external dependency, or `None` if it is a local
    /// dependency.
    pub fn external_source(&self) -> Option<&'g str> {
        match self {
            PackageSource::External(source) => Some(source),
            _ => None,
        }
    }

    /// Attempts to parse an external source.
    ///
    /// Returns `None` if the external dependency could not be recognized, or if it is a local
    /// dependency.
    ///
    /// For more about external sources, see the documentation for [`ExternalSource`](ExternalSource).
    pub fn parse_external(&self) -> Option<ExternalSource<'g>> {
        match self {
            PackageSource::External(source) => ExternalSource::new(source),
            _ => None,
        }
    }
}

impl fmt::Display for PackageSource<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PackageSource::Workspace(path) => write!(f, "{path}"),
            PackageSource::Path(path) => write!(f, "{path}"),
            PackageSource::External(source) => write!(f, "{source}"),
        }
    }
}

/// More information about an external source.
///
/// This provides information about whether an external dependency is a Git dependency or fetched
/// from a registry.
///
/// Returned by [`PackageSource::parse_external`](PackageSource::parse_external).
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum ExternalSource<'g> {
    /// This is a registry source, e.g. `"registry+https://github.com/rust-lang/crates.io-index"`.
    ///
    /// The associated data is the part of the string after the initial `"registry+"`.
    ///
    /// # Examples
    ///
    /// ```
    /// use guppy::graph::ExternalSource;
    ///
    /// let source = "registry+https://github.com/rust-lang/crates.io-index";
    /// let parsed = ExternalSource::new(source).expect("this source is understood by guppy");
    ///
    /// assert_eq!(
    ///     parsed,
    ///     ExternalSource::Registry("https://github.com/rust-lang/crates.io-index"),
    /// );
    /// ```
    Registry(&'g str),

    /// This is a registry source that uses the [sparse registry protocol][sparse], e.g. `"sparse+https://index.crates.io"`.
    ///
    /// The associated data is the part of the string after the initial `"sparse+"`.
    ///
    /// # Examples
    ///
    /// ```
    /// use guppy::graph::ExternalSource;
    ///
    /// let source = "sparse+https://index.crates.io";
    /// let parsed = ExternalSource::new(source).expect("this source is understood by guppy");
    ///
    /// assert_eq!(
    ///     parsed,
    ///     ExternalSource::Sparse("https://index.crates.io"),
    /// );
    /// ```
    ///
    /// [sparse]: https://doc.rust-lang.org/cargo/reference/registry-index.html#sparse-protocol
    Sparse(&'g str),

    /// This is a Git source.
    ///
    /// An example of a Git source string is `"git+https://github.com/rust-lang/cargo.git?branch=main#0227f048fcb7c798026ede6cc20c92befc84c3a4"`.
    /// In this case, the `Cargo.toml` would have contained:
    ///
    /// ```toml
    /// cargo = { git = "https://github.com/rust-lang/cargo.git", branch = "main" }
    /// ```
    ///
    /// and the `Cargo.lock` would have contained:
    ///
    /// ```toml
    /// [[package]]
    /// name = "cargo"
    /// version = "0.46.0"
    /// source = "git+https://github.com/rust-lang/cargo.git?branch=main#0227f048fcb7c798026ede6cc20c92befc84c3a4
    /// dependencies = [ ... ]
    /// ```
    ///
    /// For more, see [Specifying dependencies from `git` repositories](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#specifying-dependencies-from-git-repositories)
    /// in the Cargo book.
    ///
    /// # Examples
    ///
    /// ```
    /// use guppy::graph::{ExternalSource, GitReq};
    ///
    /// // A branch source.
    /// let source = "git+https://github.com/rust-lang/cargo.git?branch=main#0227f048fcb7c798026ede6cc20c92befc84c3a4";
    /// let parsed = ExternalSource::new(source).expect("this source is understood by guppy");
    ///
    /// assert_eq!(
    ///     parsed,
    ///     ExternalSource::Git {
    ///         repository: "https://github.com/rust-lang/cargo.git",
    ///         req: GitReq::Branch("main"),
    ///         resolved: "0227f048fcb7c798026ede6cc20c92befc84c3a4",
    ///     }
    /// );
    ///
    /// // A tag source.
    /// let source = "git+https://github.com/rust-lang/cargo.git?tag=v0.46.0#0227f048fcb7c798026ede6cc20c92befc84c3a4";
    /// let parsed = ExternalSource::new(source).expect("this source is understood by guppy");
    ///
    /// assert_eq!(
    ///     parsed,
    ///     ExternalSource::Git {
    ///         repository: "https://github.com/rust-lang/cargo.git",
    ///         req: GitReq::Tag("v0.46.0"),
    ///         resolved: "0227f048fcb7c798026ede6cc20c92befc84c3a4",
    ///     }
    /// );
    ///
    /// // A revision source.
    /// let source = "git+https://github.com/rust-lang/cargo.git?rev=0227f048fcb7c798026ede6cc20c92befc84c3a4#0227f048fcb7c798026ede6cc20c92befc84c3a4";
    /// let parsed = ExternalSource::new(source).expect("this source is understood by guppy");
    ///
    /// assert_eq!(
    ///     parsed,
    ///     ExternalSource::Git {
    ///         repository: "https://github.com/rust-lang/cargo.git",
    ///         req: GitReq::Rev("0227f048fcb7c798026ede6cc20c92befc84c3a4"),
    ///         resolved: "0227f048fcb7c798026ede6cc20c92befc84c3a4",
    ///     }
    /// );
    ///
    /// // A default source.
    /// let source = "git+https://github.com/gyscos/zstd-rs.git#bc874a57298bdb500cdb5aeac5f23878b6480d0b";
    /// let parsed = ExternalSource::new(source).expect("this source is understood by guppy");
    ///
    /// assert_eq!(
    ///     parsed,
    ///     ExternalSource::Git {
    ///         repository: "https://github.com/gyscos/zstd-rs.git",
    ///         req: GitReq::Default,
    ///         resolved: "bc874a57298bdb500cdb5aeac5f23878b6480d0b",
    ///     }
    /// );
    /// ```
    Git {
        /// The repository for this Git source. For the above example, this would be
        /// `"https://github.com/rust-lang/cargo.git"`.
        repository: &'g str,

        /// The revision requested in `Cargo.toml`. This may be a tag, a branch or a specific
        /// revision (commit hash).
        ///
        /// For the above example, `req` would be `GitSource::Branch("main")`.
        req: GitReq<'g>,

        /// The resolved revision, as specified in `Cargo.lock`.
        ///
        /// For the above example, `resolved_hash` would be `"0227f048fcb7c798026ede6cc20c92befc84c3a4"`.
        ///
        /// This is always a commit hash, and if `req` is `GitReq::Rev` then it is expected
        /// to be the same hash. (However, this is not verified by guppy.)
        resolved: &'g str,
    },
}

impl<'g> ExternalSource<'g> {
    /// The string `"registry+"`.
    ///
    /// Used for matching with the `Registry` variant.
    pub const REGISTRY_PLUS: &'static str = "registry+";

    /// The string `"sparse+"`.
    ///
    /// Also used for matching with the `Sparse` variant.
    pub const SPARSE_PLUS: &'static str = "sparse+";

    /// The string `"git+"`.
    ///
    /// Used for matching with the `Git` variant.
    pub const GIT_PLUS: &'static str = "git+";

    /// The string `"?branch="`.
    ///
    /// Used for matching with the `Git` variant.
    pub const BRANCH_EQ: &'static str = "?branch=";

    /// The string `"?tag="`.
    ///
    /// Used for matching with the `Git` variant.
    pub const TAG_EQ: &'static str = "?tag=";

    /// The string `"?rev="`.
    ///
    /// Used for matching with the `Git` variant.
    pub const REV_EQ: &'static str = "?rev=";

    /// The URL for the `crates.io` registry.
    ///
    /// This lacks the leading `"registry+`" that's part of the [`PackageSource`].
    pub const CRATES_IO_URL: &'static str = "https://github.com/rust-lang/crates.io-index";

    /// Attempts to parse the given string as an external source.
    ///
    /// Returns `None` if the string could not be recognized as an external source.
    pub fn new(source: &'g str) -> Option<Self> {
        // We *could* pull in a URL parsing library, but Cargo's sources are so limited that it
        // seems like a waste to.
        if let Some(registry) = source.strip_prefix(Self::REGISTRY_PLUS) {
            // A registry source.
            Some(ExternalSource::Registry(registry))
        } else if let Some(sparse) = source.strip_prefix(Self::SPARSE_PLUS) {
            // A sparse registry source.
            Some(ExternalSource::Sparse(sparse))
        } else if let Some(rest) = source.strip_prefix(Self::GIT_PLUS) {
            // A Git source.
            // Look for a trailing #, which indicates the resolved revision.
            let (rest, resolved) = rest.rsplit_once('#')?;

            let (repository, req) = if let Some(idx) = rest.find(Self::BRANCH_EQ) {
                (
                    &rest[..idx],
                    GitReq::Branch(&rest[idx + Self::BRANCH_EQ.len()..]),
                )
            } else if let Some(idx) = rest.find(Self::TAG_EQ) {
                (&rest[..idx], GitReq::Tag(&rest[idx + Self::TAG_EQ.len()..]))
            } else if let Some(idx) = rest.find(Self::REV_EQ) {
                (&rest[..idx], GitReq::Rev(&rest[idx + Self::TAG_EQ.len()..]))
            } else {
                (rest, GitReq::Default)
            };

            Some(ExternalSource::Git {
                repository,
                req,
                resolved,
            })
        } else {
            None
        }
    }
}

/// The `Display` implementation for `ExternalSource` returns the string it was constructed from.
///
/// # Examples
///
/// ```
/// use guppy::graph::{ExternalSource, GitReq};
///
/// let source = ExternalSource::Git {
///     repository: "https://github.com/rust-lang/cargo.git",
///     req: GitReq::Branch("main"),
///     resolved: "0227f048fcb7c798026ede6cc20c92befc84c3a4",
/// };
///
/// assert_eq!(
///     format!("{}", source),
///     "git+https://github.com/rust-lang/cargo.git?branch=main#0227f048fcb7c798026ede6cc20c92befc84c3a4",
/// );
/// ```
impl fmt::Display for ExternalSource<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExternalSource::Registry(url) => write!(f, "{}{}", Self::REGISTRY_PLUS, url),
            ExternalSource::Sparse(url) => write!(f, "{}{}", Self::SPARSE_PLUS, url),
            ExternalSource::Git {
                repository,
                req,
                resolved,
            } => {
                write!(f, "{}{}", Self::GIT_PLUS, repository)?;
                match req {
                    GitReq::Branch(branch) => write!(f, "{}{}", Self::BRANCH_EQ, branch)?,
                    GitReq::Tag(tag) => write!(f, "{}{}", Self::TAG_EQ, tag)?,
                    GitReq::Rev(rev) => write!(f, "{}{}", Self::REV_EQ, rev)?,
                    GitReq::Default => {}
                };
                write!(f, "#{resolved}")
            }
        }
    }
}

/// A `Cargo.toml` specification for a Git branch, tag, or revision.
///
/// For more, including examples, see the documentation for [`ExternalSource::Git`](ExternalSource::Git).
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum GitReq<'g> {
    /// A branch, e.g. `"main"`.
    ///
    /// This is specified in `Cargo.toml` as:
    ///
    /// ```toml
    /// [dependencies]
    /// cargo = { git = "...", branch = "main" }
    /// ```
    Branch(&'g str),

    /// A tag, e.g. `"guppy-0.5.0"`.
    ///
    /// This is specified in `Cargo.toml` as:
    ///
    /// ```toml
    /// [dependencies]
    /// guppy = { git = "...", tag = "guppy-0.5.0" }
    /// ```
    Tag(&'g str),

    /// A revision (commit hash), e.g. `"0227f048fcb7c798026ede6cc20c92befc84c3a4"`.
    ///
    /// This is specified in `Cargo.toml` as:
    ///
    /// ```toml
    /// [dependencies]
    /// cargo = { git = "...", rev = "0227f048fcb7c798026ede6cc20c92befc84c3a4" }
    /// ```
    Rev(&'g str),

    /// Not specified in `Cargo.toml`. Cargo treats this as the main branch by default.
    ///
    /// ```toml
    /// [dependencies]
    /// cargo = { git = "..." }
    /// ```
    Default,
}

/// Internal representation of the source of a package.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum PackageSourceImpl {
    Workspace(Box<Utf8Path>),
    Path(Box<Utf8Path>),
    // Special, common case.
    CratesIo,
    External(Box<str>),
}

/// Locations that a package can be published to.
///
/// Returned by [`PackageMetadata::publish`].
#[derive(Copy, Clone, Debug, Eq, Hash, PartialEq)]
#[non_exhaustive]
pub enum PackagePublish<'g> {
    /// Publication of this package is unrestricted.
    Unrestricted,

    /// This package can only be published to the listed [package registry].
    ///
    /// If the list is empty, this package cannot be published to any registries.
    ///
    /// [package registry]: https://doc.rust-lang.org/cargo/reference/registries.html
    Registries(&'g [String]),
}

// TODO: implement PartialOrd/Ord for these as well using lattice rules

assert_covariant!(PackagePublish);

impl<'g> PackagePublish<'g> {
    pub(super) fn new(inner: &'g PackagePublishImpl) -> Self {
        match inner {
            PackagePublishImpl::Unrestricted => PackagePublish::Unrestricted,
            PackagePublishImpl::Registries(registries) => PackagePublish::Registries(registries),
        }
    }

    /// The string `"crates-io"`, indicating that a package can be published to
    /// [crates.io](https://crates.io/).
    pub const CRATES_IO: &'static str = "crates-io";

    /// Returns true if this package can be published to any package registry.
    ///
    /// # Examples
    ///
    /// ```
    /// use guppy::graph::PackagePublish;
    ///
    /// assert!(PackagePublish::Unrestricted.is_unrestricted());
    /// assert!(!PackagePublish::Registries(&[PackagePublish::CRATES_IO.to_owned()]).is_unrestricted());
    /// assert!(!PackagePublish::Registries(&[]).is_unrestricted());
    /// ```
    pub fn is_unrestricted(&self) -> bool {
        matches!(self, PackagePublish::Unrestricted)
    }

    /// Returns true if a package can be published to the given package registry.
    ///
    /// # Examples
    ///
    /// ```
    /// use guppy::graph::PackagePublish;
    ///
    /// // Unrestricted means this package can be published to any registry.
    /// assert!(PackagePublish::Unrestricted.can_publish_to(PackagePublish::CRATES_IO));
    /// assert!(PackagePublish::Unrestricted.can_publish_to("my-registry"));
    ///
    /// // Publish to specific registries but not others.
    /// let crates_io = &[PackagePublish::CRATES_IO.to_owned()];
    /// let crates_io_publish = PackagePublish::Registries(crates_io);
    /// assert!(crates_io_publish.can_publish_to(PackagePublish::CRATES_IO));
    /// assert!(!crates_io_publish.can_publish_to("my-registry"));
    ///
    /// // Cannot publish to any registries.
    /// assert!(!PackagePublish::Registries(&[]).can_publish_to(PackagePublish::CRATES_IO));
    /// ```
    pub fn can_publish_to(&self, registry: impl AsRef<str>) -> bool {
        let registry = registry.as_ref();
        match self {
            PackagePublish::Unrestricted => true,
            PackagePublish::Registries(registries) => registries.iter().any(|r| r == registry),
        }
    }

    /// Returns true if a package can be published to crates.io.
    pub fn can_publish_to_crates_io(&self) -> bool {
        self.can_publish_to(Self::CRATES_IO)
    }

    /// Returns true if a package cannot be published to any registries.
    ///
    /// # Examples
    ///
    /// ```
    /// use guppy::graph::PackagePublish;
    ///
    /// assert!(!PackagePublish::Unrestricted.is_never());
    /// assert!(!PackagePublish::Registries(&[PackagePublish::CRATES_IO.to_owned()]).is_never());
    /// assert!(PackagePublish::Registries(&[]).is_never());
    /// ```
    pub fn is_never(&self) -> bool {
        match self {
            PackagePublish::Unrestricted => false,
            PackagePublish::Registries(registries) => registries.is_empty(),
        }
    }
}

/// Internal representation of PackagePublish.
#[derive(Clone, Debug)]
pub(super) enum PackagePublishImpl {
    Unrestricted,
    Registries(Box<[String]>),
}

/// Represents a dependency from one package to another.
///
/// This struct contains information about:
/// * whether this dependency was renamed in the context of this crate.
/// * if this is a normal, dev and/or build dependency.
/// * platform-specific information about required, optional and status
#[derive(Copy, Clone, Debug)]
pub struct PackageLink<'g> {
    graph: &'g PackageGraph,
    from: &'g PackageMetadataImpl,
    to: &'g PackageMetadataImpl,
    edge_ix: EdgeIndex<PackageIx>,
    inner: &'g PackageLinkImpl,
}

assert_covariant!(PackageLink);

impl<'g> PackageLink<'g> {
    pub(super) fn new(
        graph: &'g PackageGraph,
        source_ix: NodeIndex<PackageIx>,
        target_ix: NodeIndex<PackageIx>,
        edge_ix: EdgeIndex<PackageIx>,
        inner: Option<&'g PackageLinkImpl>,
    ) -> Self {
        let from = graph
            .data
            .metadata_impl(&graph.dep_graph[source_ix])
            .expect("'from' should have associated metadata");
        let to = graph
            .data
            .metadata_impl(&graph.dep_graph[target_ix])
            .expect("'to' should have associated metadata");
        Self {
            graph,
            from,
            to,
            edge_ix,
            inner: inner.unwrap_or_else(|| &graph.dep_graph[edge_ix]),
        }
    }

    /// Returns the package which depends on the `to` package.
    pub fn from(&self) -> PackageMetadata<'g> {
        PackageMetadata::new(self.graph, self.from)
    }

    /// Returns the package which is depended on by the `from` package.
    pub fn to(&self) -> PackageMetadata<'g> {
        PackageMetadata::new(self.graph, self.to)
    }

    /// Returns the endpoints as a pair of packages `(from, to)`.
    pub fn endpoints(&self) -> (PackageMetadata<'g>, PackageMetadata<'g>) {
        (self.from(), self.to())
    }

    /// Returns the name for this dependency edge. This can be affected by a crate rename.
    pub fn dep_name(&self) -> &'g str {
        &self.inner.dep_name
    }

    /// Returns the resolved name for this dependency edge. This may involve renaming the crate and
    /// replacing - with _.
    pub fn resolved_name(&self) -> &'g str {
        &self.inner.resolved_name
    }

    /// Returns the semver requirements specified for this dependency.
    ///
    /// To get the resolved version, see the `to` field of the `PackageLink` this was part of.
    ///
    /// ## Notes
    ///
    /// A dependency can be requested multiple times, possibly with different version requirements,
    /// even if they all end up resolving to the same version. `version_req` will return any of
    /// those requirements.
    ///
    /// See [Specifying Dependencies](https://doc.rust-lang.org/cargo/reference/specifying-dependencies.html#specifying-dependencies)
    /// in the Cargo reference for more details.
    pub fn version_req(&self) -> &'g VersionReq {
        &self.inner.version_req
    }

    /// Returns the registry URL for this dependency, if specified.
    ///
    /// Returns `None` for dependencies from crates.io (the default registry) or
    /// for dependencies without an explicit registry.
    pub fn registry(&self) -> Option<&'g str> {
        self.inner.registry.as_deref()
    }

    /// Returns the file system path for this dependency, if it is a path
    /// dependency.
    ///
    /// Returns `None` for dependencies from registries or other sources.
    pub fn path(&self) -> Option<&'g Utf8Path> {
        self.inner.path.as_deref()
    }

    /// Returns details about this dependency from the `[dependencies]` section.
    pub fn normal(&self) -> DependencyReq<'g> {
        DependencyReq {
            inner: &self.inner.normal,
        }
    }

    /// Returns details about this dependency from the `[build-dependencies]` section.
    pub fn build(&self) -> DependencyReq<'g> {
        DependencyReq {
            inner: &self.inner.build,
        }
    }

    /// Returns details about this dependency from the `[dev-dependencies]` section.
    pub fn dev(&self) -> DependencyReq<'g> {
        DependencyReq {
            inner: &self.inner.dev,
        }
    }

    /// Returns details about this dependency from the section specified by the given dependency
    /// kind.
    pub fn req_for_kind(&self, kind: DependencyKind) -> DependencyReq<'g> {
        match kind {
            DependencyKind::Normal => self.normal(),
            DependencyKind::Development => self.dev(),
            DependencyKind::Build => self.build(),
        }
    }

    /// Return true if this edge is dev-only, i.e. code from this edge will not be included in
    /// normal builds.
    pub fn dev_only(&self) -> bool {
        self.inner.dev_only()
    }

    // ---
    // Helper methods
    // ---

    /// Returns the edge index.
    #[allow(dead_code)]
    pub(super) fn edge_ix(&self) -> EdgeIndex<PackageIx> {
        self.edge_ix
    }

    /// Returns (source, target, edge) as a triple of pointers. Useful for testing.
    #[doc(hidden)]
    pub fn as_inner_ptrs(&self) -> PackageLinkPtrs {
        PackageLinkPtrs {
            from: self.from,
            to: self.to,
            inner: self.inner,
        }
    }
}

/// An opaque identifier for a PackageLink's pointers. Used for tests.
#[derive(Copy, Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
#[doc(hidden)]
pub struct PackageLinkPtrs {
    from: *const PackageMetadataImpl,
    to: *const PackageMetadataImpl,
    inner: *const PackageLinkImpl,
}

#[derive(Clone, Debug)]
pub(crate) struct PackageLinkImpl {
    pub(super) dep_name: String,
    pub(super) resolved_name: String,
    pub(super) version_req: VersionReq,
    pub(super) registry: Option<String>,
    pub(super) path: Option<Utf8PathBuf>,
    pub(super) normal: DependencyReqImpl,
    pub(super) build: DependencyReqImpl,
    pub(super) dev: DependencyReqImpl,
}

impl PackageLinkImpl {
    #[inline]
    fn dev_only(&self) -> bool {
        self.normal.enabled().is_never() && self.build.enabled().is_never()
    }
}

/// Information about a specific kind of dependency (normal, build or dev) from a package to another
/// package.
///
/// Usually found within the context of a [`PackageLink`](struct.PackageLink.html).
#[derive(Clone, Debug)]
pub struct DependencyReq<'g> {
    pub(super) inner: &'g DependencyReqImpl,
}

impl<'g> DependencyReq<'g> {
    /// Returns true if there is at least one `Cargo.toml` entry corresponding to this requirement.
    ///
    /// For example, if this dependency is specified in the `[dev-dependencies]` section,
    /// `edge.dev().is_present()` will return true.
    pub fn is_present(&self) -> bool {
        !self.inner.enabled().is_never()
    }

    /// Returns the enabled status of this dependency.
    ///
    /// `status` is the union of `default_features` and `no_default_features`.
    ///
    /// See the documentation for `EnabledStatus` for more.
    pub fn status(&self) -> EnabledStatus<'g> {
        self.inner.enabled()
    }

    /// Returns the enabled status of this dependency when `default-features = true`.
    ///
    /// See the documentation for `EnabledStatus` for more.
    pub fn default_features(&self) -> EnabledStatus<'g> {
        self.inner.default_features()
    }

    /// Returns the enabled status of this dependency when `default-features = false`.
    ///
    /// This is generally less useful than `status` or `default_features`, but is provided for
    /// completeness.
    ///
    /// See the documentation for `EnabledStatus` for more.
    pub fn no_default_features(&self) -> EnabledStatus<'g> {
        self.inner.no_default_features()
    }

    /// Returns a list of all features possibly enabled by this dependency. This includes features
    /// that are only turned on if the dependency is optional, or features enabled by inactive
    /// platforms.
    pub fn features(&self) -> impl Iterator<Item = &'g str> + use<'g> {
        self.inner.all_features()
    }

    /// Returns the enabled status of this feature.
    ///
    /// Note that as of Rust 1.42, the default feature resolver behaves in potentially surprising
    /// ways. See the [Cargo
    /// reference](https://doc.rust-lang.org/nightly/cargo/reference/unstable.html#features) for
    /// more.
    ///
    /// See the documentation for `EnabledStatus` for more.
    pub fn feature_status(&self, feature: &str) -> EnabledStatus<'g> {
        self.inner.feature_status(feature)
    }
}

/// Whether a dependency or feature is required, optional, or disabled.
///
/// Returned by the methods on `DependencyMetadata`.
///
/// ## Examples
///
/// ```toml
/// [dependencies]
/// once_cell = "1"
/// ```
///
/// The dependency and default features are *required* on all platforms.
///
/// ```toml
/// [dependencies]
/// once_cell = { version = "1", optional = true }
/// ```
///
/// The dependency and default features are *optional* on all platforms.
///
/// ```toml
/// [target.'cfg(windows)'.dependencies]
/// once_cell = { version = "1", optional = true }
/// ```
///
/// The result is platform-dependent. On Windows, the dependency and default features are both
/// *optional*. On non-Windows platforms, the dependency and default features are *disabled*.
///
/// ```toml
/// [dependencies]
/// once_cell = { version = "1", optional = true }
///
/// [target.'cfg(windows)'.dependencies]
/// once_cell = { version = "1", optional = false, default-features = false }
/// ```
///
/// The result is platform-dependent. On Windows, the dependency is *mandatory* and default features
/// are *optional* (i.e. enabled if the `once_cell` feature is turned on).
///
/// On Unix platforms, the dependency and default features are both *optional*.
#[derive(Copy, Clone, Debug)]
pub struct EnabledStatus<'g> {
    required: PlatformStatus<'g>,
    optional: PlatformStatus<'g>,
}

assert_covariant!(EnabledStatus);

impl<'g> EnabledStatus<'g> {
    pub(super) fn new(required: &'g PlatformStatusImpl, optional: &'g PlatformStatusImpl) -> Self {
        Self {
            required: PlatformStatus::new(required),
            optional: PlatformStatus::new(optional),
        }
    }

    /// Returns true if this dependency is never enabled on any platform.
    pub fn is_never(&self) -> bool {
        self.required.is_never() && self.optional.is_never()
    }

    /// Evaluates whether this dependency is required on the given platform spec.
    ///
    /// Returns `Unknown` if the result was unknown, which may happen if evaluating against an
    /// individual platform and its target features are unknown.
    pub fn required_on(&self, platform_spec: &PlatformSpec) -> EnabledTernary {
        self.required.enabled_on(platform_spec)
    }

    /// Evaluates whether this dependency is enabled (required or optional) on the given platform
    /// spec.
    ///
    /// Returns `Unknown` if the result was unknown, which may happen if evaluating against an
    /// individual platform and its target features are unknown.
    pub fn enabled_on(&self, platform_spec: &PlatformSpec) -> EnabledTernary {
        let required = self.required.enabled_on(platform_spec);
        let optional = self.optional.enabled_on(platform_spec);

        required | optional
    }

    /// Returns the `PlatformStatus` corresponding to whether this dependency is required.
    pub fn required_status(&self) -> PlatformStatus<'g> {
        self.required
    }

    /// Returns the `PlatformStatus` corresponding to whether this dependency is optional.
    pub fn optional_status(&self) -> PlatformStatus<'g> {
        self.optional
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(super) enum NamedFeatureDep {
    NamedFeature(Box<str>),
    OptionalDependency(Box<str>),
    DependencyNamedFeature {
        dep_name: Box<str>,
        feature: Box<str>,
        weak: bool,
    },
}

impl NamedFeatureDep {
    #[inline]
    pub(super) fn named_feature(feature_name: impl Into<String>) -> Self {
        Self::NamedFeature(feature_name.into().into_boxed_str())
    }

    #[inline]
    pub(super) fn optional_dependency(dep_name: impl Into<String>) -> Self {
        Self::OptionalDependency(dep_name.into().into_boxed_str())
    }

    #[inline]
    pub(super) fn dep_named_feature(
        dep_name: impl Into<String>,
        feature: impl Into<String>,
        weak: bool,
    ) -> Self {
        Self::DependencyNamedFeature {
            dep_name: dep_name.into().into_boxed_str(),
            feature: feature.into().into_boxed_str(),
            weak,
        }
    }
}

impl fmt::Display for NamedFeatureDep {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::NamedFeature(feature) => write!(f, "{feature}"),
            Self::OptionalDependency(dep_name) => write!(f, "dep:{dep_name}"),
            Self::DependencyNamedFeature {
                dep_name,
                feature,
                weak,
            } => {
                write!(
                    f,
                    "{}{}/{}",
                    dep_name,
                    if *weak { "?" } else { "" },
                    feature
                )
            }
        }
    }
}

/// Information about dependency requirements.
#[derive(Clone, Debug, Default)]
pub(super) struct DependencyReqImpl {
    pub(super) required: DepRequiredOrOptional,
    pub(super) optional: DepRequiredOrOptional,
}

impl DependencyReqImpl {
    fn all_features(&self) -> impl Iterator<Item = &str> {
        self.required
            .all_features()
            .chain(self.optional.all_features())
    }

    pub(super) fn enabled(&self) -> EnabledStatus<'_> {
        self.make_status(|req_impl| &req_impl.build_if)
    }

    pub(super) fn default_features(&self) -> EnabledStatus<'_> {
        self.make_status(|req_impl| &req_impl.default_features_if)
    }

    pub(super) fn no_default_features(&self) -> EnabledStatus<'_> {
        self.make_status(|req_impl| &req_impl.no_default_features_if)
    }

    pub(super) fn feature_status(&self, feature: &str) -> EnabledStatus<'_> {
        // This PlatformStatusImpl in static memory is so that the lifetimes work out.
        static DEFAULT_STATUS: PlatformStatusImpl = PlatformStatusImpl::Specs(Vec::new());

        self.make_status(|req_impl| {
            req_impl
                .feature_targets
                .get(feature)
                .unwrap_or(&DEFAULT_STATUS)
        })
    }

    fn make_status(
        &self,
        pred_fn: impl Fn(&DepRequiredOrOptional) -> &PlatformStatusImpl,
    ) -> EnabledStatus<'_> {
        EnabledStatus::new(pred_fn(&self.required), pred_fn(&self.optional))
    }
}

/// Information about dependency requirements, scoped to either the dependency being required or
/// optional.
#[derive(Clone, Debug, Default)]
pub(super) struct DepRequiredOrOptional {
    pub(super) build_if: PlatformStatusImpl,
    pub(super) default_features_if: PlatformStatusImpl,
    pub(super) no_default_features_if: PlatformStatusImpl,
    pub(super) feature_targets: BTreeMap<String, PlatformStatusImpl>,
}

impl DepRequiredOrOptional {
    pub(super) fn all_features(&self) -> impl Iterator<Item = &str> {
        self.feature_targets.keys().map(|s| s.as_str())
    }
}
