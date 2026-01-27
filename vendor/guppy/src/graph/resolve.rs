// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    Error, PackageId,
    debug_ignore::DebugIgnore,
    graph::{
        DependencyDirection, PackageGraph, PackageIx, PackageLink, PackageLinkImpl,
        PackageMetadata, PackageQuery,
        feature::{FeatureFilter, FeatureSet},
        resolve_core::{ResolveCore, Topo},
    },
    petgraph_support::{
        IxBitSet,
        dot::{DotFmt, DotVisitor, DotWrite},
        edge_ref::GraphEdgeRef,
    },
    sorted_set::SortedSet,
};
use camino::Utf8Path;
use fixedbitset::FixedBitSet;
use petgraph::{
    prelude::*,
    visit::{NodeFiltered, NodeRef},
};
use std::fmt;

impl PackageGraph {
    /// Creates a new `PackageSet` consisting of all members of this package graph.
    ///
    /// This is normally the same as `query_workspace().resolve()`, but can differ if packages have
    /// been replaced with `[patch]` or `[replace]`.
    ///
    /// In most situations, `query_workspace` is preferred. Use `resolve_all` if you know you need
    /// parts of the graph that aren't accessible from the workspace.
    pub fn resolve_all(&self) -> PackageSet<'_> {
        PackageSet {
            graph: DebugIgnore(self),
            core: ResolveCore::all_nodes(&self.dep_graph),
        }
    }

    /// Creates a new, empty `PackageSet` associated with this package graph.
    pub fn resolve_none(&self) -> PackageSet<'_> {
        PackageSet {
            graph: DebugIgnore(self),
            core: ResolveCore::empty(),
        }
    }

    /// Creates a new `PackageSet` consisting of the specified package IDs.
    ///
    /// This does not include transitive dependencies. To do so, use the `query_` methods.
    ///
    /// Returns an error if any package IDs are unknown.
    pub fn resolve_ids<'a>(
        &self,
        package_ids: impl IntoIterator<Item = &'a PackageId>,
    ) -> Result<PackageSet<'_>, Error> {
        Ok(PackageSet {
            graph: DebugIgnore(self),
            core: ResolveCore::from_included::<IxBitSet>(self.package_ixs(package_ids)?),
        })
    }

    /// Creates a new `PackageSet` consisting of all packages in this workspace.
    ///
    /// This does not include transitive dependencies. To do so, use `query_workspace`.
    pub fn resolve_workspace(&self) -> PackageSet<'_> {
        let included: IxBitSet = self
            .workspace()
            .iter_by_path()
            .map(|(_, package)| package.package_ix())
            .collect();
        PackageSet {
            graph: DebugIgnore(self),
            core: ResolveCore::from_included(included),
        }
    }

    /// Creates a new `PackageSet` consisting of the specified workspace packages by path.
    ///
    /// This does not include transitive dependencies. To do so, use `query_workspace_paths`.
    ///
    /// Returns an error if any workspace paths were unknown.
    pub fn resolve_workspace_paths(
        &self,
        paths: impl IntoIterator<Item = impl AsRef<Utf8Path>>,
    ) -> Result<PackageSet<'_>, Error> {
        let workspace = self.workspace();
        let included: IxBitSet = paths
            .into_iter()
            .map(|path| {
                workspace
                    .member_by_path(path.as_ref())
                    .map(|package| package.package_ix())
            })
            .collect::<Result<_, Error>>()?;
        Ok(PackageSet {
            graph: DebugIgnore(self),
            core: ResolveCore::from_included(included),
        })
    }

    /// Creates a new `PackageSet` consisting of the specified workspace packages by name.
    ///
    /// This does not include transitive dependencies. To do so, use `query_workspace_names`.
    ///
    /// Returns an error if any package names were unknown.
    pub fn resolve_workspace_names(
        &self,
        names: impl IntoIterator<Item = impl AsRef<str>>,
    ) -> Result<PackageSet<'_>, Error> {
        let workspace = self.workspace();
        let included: IxBitSet = names
            .into_iter()
            .map(|name| {
                workspace
                    .member_by_name(name.as_ref())
                    .map(|package| package.package_ix())
            })
            .collect::<Result<_, _>>()?;
        Ok(PackageSet {
            graph: DebugIgnore(self),
            core: ResolveCore::from_included(included),
        })
    }

    /// Creates a new `PackageSet` consisting of packages with the given name.
    ///
    /// The result is empty if there are no packages with the given name.
    pub fn resolve_package_name(&self, name: impl AsRef<str>) -> PackageSet<'_> {
        // Turns out that for reasonably-sized graphs, a linear search across package names is
        // extremely fast: much faster than trying to do something fancy like use an FST or trie.
        //
        // TODO: optimize this in the future, possibly through some sort of hashmap variant that
        // doesn't require a borrow.
        let name = name.as_ref();
        let included: IxBitSet = self
            .packages()
            .filter_map(|package| {
                if package.name() == name {
                    Some(package.package_ix())
                } else {
                    None
                }
            })
            .collect();
        PackageSet::from_included(self, included)
    }
}

/// A set of resolved packages in a package graph.
///
/// Created by `PackageQuery::resolve`.
#[derive(Clone, Debug)]
pub struct PackageSet<'g> {
    graph: DebugIgnore<&'g PackageGraph>,
    core: ResolveCore<PackageGraph>,
}

assert_covariant!(PackageSet);

impl<'g> PackageSet<'g> {
    pub(super) fn new(query: PackageQuery<'g>) -> Self {
        let graph = query.graph;
        Self {
            graph: DebugIgnore(graph),
            core: ResolveCore::new(graph.dep_graph(), query.params),
        }
    }

    pub(super) fn from_included(graph: &'g PackageGraph, included: impl Into<FixedBitSet>) -> Self {
        Self {
            graph: DebugIgnore(graph),
            core: ResolveCore::from_included(included),
        }
    }

    pub(super) fn with_resolver(
        query: PackageQuery<'g>,
        mut resolver: impl PackageResolver<'g>,
    ) -> Self {
        let graph = query.graph;
        let params = query.params.clone();
        Self {
            graph: DebugIgnore(graph),
            core: ResolveCore::with_edge_filter(graph.dep_graph(), params, |edge| {
                let link = graph.edge_ref_to_link(edge);
                resolver.accept(&query, link)
            }),
        }
    }

    /// Returns the number of packages in this set.
    pub fn len(&self) -> usize {
        self.core.len()
    }

    /// Returns true if no packages were resolved in this set.
    pub fn is_empty(&self) -> bool {
        self.core.is_empty()
    }

    /// Returns true if this package ID is contained in this resolve set.
    ///
    /// Returns an error if the package ID is unknown.
    pub fn contains(&self, package_id: &PackageId) -> Result<bool, Error> {
        Ok(self.contains_ix(self.graph.package_ix(package_id)?))
    }

    /// Creates a new `PackageQuery` from this set in the specified direction.
    ///
    /// This is equivalent to constructing a query from all the `package_ids`.
    pub fn to_package_query(&self, direction: DependencyDirection) -> PackageQuery<'g> {
        let package_ixs = SortedSet::new(
            self.core
                .included
                .ones()
                .map(NodeIndex::new)
                .collect::<Vec<_>>(),
        );
        self.graph.query_from_parts(package_ixs, direction)
    }

    // ---
    // Set operations
    // ---

    /// Returns a `PackageSet` that contains all packages present in at least one of `self`
    /// and `other`.
    ///
    /// ## Panics
    ///
    /// Panics if the package graphs associated with `self` and `other` don't match.
    pub fn union(&self, other: &Self) -> Self {
        assert!(
            ::std::ptr::eq(self.graph.0, other.graph.0),
            "package graphs passed into union() match"
        );
        let mut res = self.clone();
        res.core.union_with(&other.core);
        res
    }

    /// Returns a `PackageSet` that contains all packages present in both `self` and `other`.
    ///
    /// ## Panics
    ///
    /// Panics if the package graphs associated with `self` and `other` don't match.
    pub fn intersection(&self, other: &Self) -> Self {
        assert!(
            ::std::ptr::eq(self.graph.0, other.graph.0),
            "package graphs passed into intersection() match"
        );
        let mut res = self.clone();
        res.core.intersect_with(&other.core);
        res
    }

    /// Returns a `PackageSet` that contains all packages present in `self` but not `other`.
    ///
    /// ## Panics
    ///
    /// Panics if the package graphs associated with `self` and `other` don't match.
    pub fn difference(&self, other: &Self) -> Self {
        assert!(
            ::std::ptr::eq(self.graph.0, other.graph.0),
            "package graphs passed into difference() match"
        );
        Self {
            graph: self.graph,
            core: self.core.difference(&other.core),
        }
    }

    /// Returns a `PackageSet` that contains all packages present in exactly one of `self` and
    /// `other`.
    ///
    /// ## Panics
    ///
    /// Panics if the package graphs associated with `self` and `other` don't match.
    pub fn symmetric_difference(&self, other: &Self) -> Self {
        assert!(
            ::std::ptr::eq(self.graph.0, other.graph.0),
            "package graphs passed into symmetric_difference() match"
        );
        let mut res = self.clone();
        res.core.symmetric_difference_with(&other.core);
        res
    }

    /// Returns a `PackageSet` on which a filter has been applied.
    ///
    /// Filters out all values for which the callback returns false.
    ///
    /// ## Cycles
    ///
    /// For packages within a dependency cycle, the callback will be called in non-dev order. When
    /// the direction is forward, if package Foo has a dependency on Bar, and Bar has a cyclic
    /// dev-dependency on Foo, then Foo is returned before Bar.
    pub fn filter(
        &self,
        direction: DependencyDirection,
        mut callback: impl FnMut(PackageMetadata<'g>) -> bool,
    ) -> Self {
        let graph = *self.graph;
        let included: IxBitSet = self
            .packages(direction)
            .filter_map(move |package| {
                let package_ix = package.package_ix();
                if callback(package) {
                    Some(package_ix)
                } else {
                    None
                }
            })
            .collect();
        Self::from_included(graph, included)
    }

    /// Partitions this `PackageSet` into two.
    ///
    /// The first `PackageSet` contains packages for which the callback returned true, and the
    /// second one contains packages for which the callback returned false.
    ///
    /// ## Cycles
    ///
    /// For packages within a dependency cycle, the callback will be called in non-dev order. When
    /// the direction is forward, if package Foo has a dependency on Bar, and Bar has a cyclic
    /// dev-dependency on Foo, then Foo is returned before Bar.
    pub fn partition(
        &self,
        direction: DependencyDirection,
        mut callback: impl FnMut(PackageMetadata<'g>) -> bool,
    ) -> (Self, Self) {
        let graph = *self.graph;
        let mut left = IxBitSet::with_capacity(self.core.included.len());
        let mut right = left.clone();

        self.packages(direction).for_each(|package| {
            let package_ix = package.package_ix();
            match callback(package) {
                true => left.insert_node_ix(package_ix),
                false => right.insert_node_ix(package_ix),
            }
        });
        (
            Self::from_included(graph, left),
            Self::from_included(graph, right),
        )
    }

    /// Performs filtering and partitioning at the same time.
    ///
    /// The first `PackageSet` contains packages for which the callback returned `Some(true)`, and
    /// the second one contains packages for which the callback returned `Some(false)`. Packages
    /// for which the callback returned `None` are dropped.
    ///
    /// ## Cycles
    ///
    /// For packages within a dependency cycle, the callback will be called in non-dev order. When
    /// the direction is forward, if package Foo has a dependency on Bar, and Bar has a cyclic
    /// dev-dependency on Foo, then Foo is returned before Bar.
    pub fn filter_partition(
        &self,
        direction: DependencyDirection,
        mut callback: impl FnMut(PackageMetadata<'g>) -> Option<bool>,
    ) -> (Self, Self) {
        let graph = *self.graph;
        let mut left = IxBitSet::with_capacity(self.core.included.len());
        let mut right = left.clone();

        self.packages(direction).for_each(|package| {
            let package_ix = package.package_ix();
            match callback(package) {
                Some(true) => left.insert_node_ix(package_ix),
                Some(false) => right.insert_node_ix(package_ix),
                None => {}
            }
        });
        (
            Self::from_included(graph, left),
            Self::from_included(graph, right),
        )
    }

    // ---
    // Conversion to FeatureSet
    // ---

    /// Creates a new `FeatureSet` consisting of all packages in this `PackageSet`, using the given
    /// feature filter.
    ///
    /// This will cause the feature graph to be constructed if it hasn't been done so already.
    pub fn to_feature_set(&self, filter: impl FeatureFilter<'g>) -> FeatureSet<'g> {
        let feature_graph = self.graph.feature_graph();
        let included: IxBitSet = feature_graph.feature_ixs_for_package_ixs_filtered(
            // The direction of iteration doesn't matter.
            self.ixs(DependencyDirection::Forward),
            filter,
        );
        FeatureSet::from_included(feature_graph, included)
    }

    // ---
    // Iterators
    // ---

    /// Iterates over package IDs, in topological order in the direction specified.
    ///
    /// ## Cycles
    ///
    /// The packages within a dependency cycle will be returned in non-dev order. When the direction
    /// is forward, if package Foo has a dependency on Bar, and Bar has a cyclic dev-dependency on
    /// Foo, then Foo is returned before Bar.
    pub fn package_ids<'a>(
        &'a self,
        direction: DependencyDirection,
    ) -> impl ExactSizeIterator<Item = &'g PackageId> + 'a {
        let graph = self.graph;
        self.core
            .topo(self.graph.sccs(), direction)
            .map(move |package_ix| &graph.dep_graph[package_ix])
    }

    pub(super) fn ixs(&'g self, direction: DependencyDirection) -> Topo<'g, PackageGraph> {
        self.core.topo(self.graph.sccs(), direction)
    }

    /// Iterates over package metadatas, in topological order in the direction specified.
    ///
    /// ## Cycles
    ///
    /// The packages within a dependency cycle will be returned in non-dev order. When the direction
    /// is forward, if package Foo has a dependency on Bar, and Bar has a cyclic dev-dependency on
    /// Foo, then Foo is returned before Bar.
    pub fn packages<'a>(
        &'a self,
        direction: DependencyDirection,
    ) -> impl ExactSizeIterator<Item = PackageMetadata<'g>> + 'a {
        let graph = self.graph;
        self.package_ids(direction)
            .map(move |package_id| graph.metadata(package_id).expect("known package IDs"))
    }

    /// Returns the set of "root package" IDs in the specified direction.
    ///
    /// * If direction is Forward, return the set of packages that do not have any dependencies
    ///   within the selected graph.
    /// * If direction is Reverse, return the set of packages that do not have any dependents within
    ///   the selected graph.
    ///
    /// ## Cycles
    ///
    /// If a root consists of a dependency cycle, all the packages in it will be returned in
    /// non-dev order (when the direction is forward).
    pub fn root_ids<'a>(
        &'a self,
        direction: DependencyDirection,
    ) -> impl ExactSizeIterator<Item = &'g PackageId> + 'a {
        let dep_graph = &self.graph.dep_graph;
        self.core
            .roots(self.graph.dep_graph(), self.graph.sccs(), direction)
            .into_iter()
            .map(move |package_ix| &dep_graph[package_ix])
    }

    /// Returns the set of "root package" metadatas in the specified direction.
    ///
    /// * If direction is Forward, return the set of packages that do not have any dependencies
    ///   within the selected graph.
    /// * If direction is Reverse, return the set of packages that do not have any dependents within
    ///   the selected graph.
    ///
    /// ## Cycles
    ///
    /// If a root consists of a dependency cycle, all the packages in it will be returned in
    /// non-dev order (when the direction is forward).
    pub fn root_packages<'a>(
        &'a self,
        direction: DependencyDirection,
    ) -> impl ExactSizeIterator<Item = PackageMetadata<'g>> + 'a {
        let package_graph = self.graph;
        self.core
            .roots(self.graph.dep_graph(), self.graph.sccs(), direction)
            .into_iter()
            .map(move |package_ix| {
                package_graph
                    .metadata(&package_graph.dep_graph[package_ix])
                    .expect("invalid node index")
            })
    }

    /// Creates an iterator over `PackageLink` instances.
    ///
    /// If the iteration is in forward order, for any given package, at least one link where the
    /// package is on the `to` end is returned before any links where the package is on the
    /// `from` end.
    ///
    /// If the iteration is in reverse order, for any given package, at least one link where the
    /// package is on the `from` end is returned before any links where the package is on the `to`
    /// end.
    ///
    /// ## Cycles
    ///
    /// The links in a dependency cycle will be returned in non-dev order. When the direction is
    /// forward, if package Foo has a dependency on Bar, and Bar has a cyclic dev-dependency on Foo,
    /// then the link Foo -> Bar is returned before the link Bar -> Foo.
    pub fn links<'a>(
        &'a self,
        direction: DependencyDirection,
    ) -> impl Iterator<Item = PackageLink<'g>> + 'a {
        let graph = self.graph.0;
        self.core
            .links(graph.dep_graph(), graph.sccs(), direction)
            .map(move |(source_ix, target_ix, edge_ix)| {
                PackageLink::new(graph, source_ix, target_ix, edge_ix, None)
            })
    }

    /// Constructs a representation of the selected packages in `dot` format.
    pub fn display_dot<'a, V: PackageDotVisitor + 'g>(
        &'a self,
        visitor: V,
    ) -> impl fmt::Display + 'a {
        let node_filtered = NodeFiltered(self.graph.dep_graph(), &self.core.included);
        DotFmt::new(node_filtered, VisitorWrap::new(self.graph.0, visitor))
    }

    // ---
    // Helper methods
    // ---

    /// Returns all the package ixs without topologically sorting them.
    #[allow(dead_code)]
    pub(super) fn ixs_unordered(&self) -> impl Iterator<Item = NodeIndex<PackageIx>> + '_ {
        self.core.included.ones().map(NodeIndex::new)
    }

    pub(super) fn contains_ix(&self, package_ix: NodeIndex<PackageIx>) -> bool {
        self.core.contains(package_ix)
    }
}

impl PartialEq for PackageSet<'_> {
    fn eq(&self, other: &Self) -> bool {
        ::std::ptr::eq(self.graph.0, other.graph.0) && self.core == other.core
    }
}

impl Eq for PackageSet<'_> {}

/// Represents whether a particular link within a package graph should be followed during a
/// resolve operation.
pub trait PackageResolver<'g> {
    /// Returns true if this link should be followed during a resolve operation.
    ///
    /// Returning false does not prevent the `to` package (or `from` package with `query_reverse`)
    /// from being included if it's reachable through other means.
    fn accept(&mut self, query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool;
}

impl<'g, T> PackageResolver<'g> for &mut T
where
    T: PackageResolver<'g>,
{
    fn accept(&mut self, query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool {
        (**self).accept(query, link)
    }
}

impl<'g> PackageResolver<'g> for Box<dyn PackageResolver<'g> + '_> {
    fn accept(&mut self, query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool {
        (**self).accept(query, link)
    }
}

impl<'g> PackageResolver<'g> for &mut dyn PackageResolver<'g> {
    fn accept(&mut self, query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool {
        (**self).accept(query, link)
    }
}

pub(super) struct ResolverFn<F>(pub(super) F);

impl<'g, F> PackageResolver<'g> for ResolverFn<F>
where
    F: FnMut(&PackageQuery<'g>, PackageLink<'g>) -> bool,
{
    fn accept(&mut self, query: &PackageQuery<'g>, link: PackageLink<'g>) -> bool {
        (self.0)(query, link)
    }
}

/// A visitor used for formatting `dot` graphs.
pub trait PackageDotVisitor {
    /// Visits this package. The implementation may output a label for this package to the given
    /// `DotWrite`.
    fn visit_package(&self, package: PackageMetadata<'_>, f: &mut DotWrite<'_, '_>) -> fmt::Result;

    /// Visits this dependency link. The implementation may output a label for this link to the
    /// given `DotWrite`.
    fn visit_link(&self, link: PackageLink<'_>, f: &mut DotWrite<'_, '_>) -> fmt::Result;
}

struct VisitorWrap<'g, V> {
    graph: &'g PackageGraph,
    inner: V,
}

impl<'g, V> VisitorWrap<'g, V> {
    fn new(graph: &'g PackageGraph, inner: V) -> Self {
        Self { graph, inner }
    }
}

impl<'g, V, NR, ER> DotVisitor<NR, ER> for VisitorWrap<'g, V>
where
    V: PackageDotVisitor,
    NR: NodeRef<NodeId = NodeIndex<PackageIx>, Weight = PackageId>,
    ER: GraphEdgeRef<'g, PackageLinkImpl, PackageIx>,
{
    fn visit_node(&self, node: NR, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        let metadata = self
            .graph
            .metadata(node.weight())
            .expect("visited node should have associated metadata");
        self.inner.visit_package(metadata, f)
    }

    fn visit_edge(&self, edge: ER, f: &mut DotWrite<'_, '_>) -> fmt::Result {
        let link = self.graph.edge_ref_to_link(edge.into_edge_reference());
        self.inner.visit_link(link, f)
    }
}
