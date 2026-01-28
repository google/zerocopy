// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    Error, PackageId,
    graph::{
        DependencyDirection, PackageGraph, PackageIx, PackageLink, PackageMetadata,
        PackageResolver, PackageSet, ResolverFn,
        feature::{FeatureFilter, FeatureQuery},
        query_core::QueryParams,
    },
    sorted_set::SortedSet,
};
use camino::Utf8Path;
use petgraph::prelude::*;

/// A query over a package graph.
///
/// This is the entry point for iterators over IDs and dependency links, and dot graph presentation.
/// A `PackageQuery` is constructed through the `query_` methods on `PackageGraph`.
#[derive(Clone, Debug)]
pub struct PackageQuery<'g> {
    // The fields are pub(super) for access within the graph module.
    pub(super) graph: &'g PackageGraph,
    pub(super) params: QueryParams<PackageGraph>,
}

assert_covariant!(PackageQuery);

/// ## Queries
///
/// The methods in this section create *queries* over subsets of this package graph. Use the methods
/// here to analyze transitive dependencies.
impl PackageGraph {
    /// Creates a new forward query over the entire workspace.
    ///
    /// `query_workspace` will select all workspace packages and their transitive dependencies. To
    /// create a `PackageSet` with just workspace packages, use `resolve_workspace`.
    pub fn query_workspace(&self) -> PackageQuery<'_> {
        self.query_forward(self.workspace().member_ids())
            .expect("workspace packages should all be known")
    }

    /// Creates a new forward query over the specified workspace packages by path.
    ///
    /// Returns an error if any workspace paths were unknown.
    pub fn query_workspace_paths(
        &self,
        paths: impl IntoIterator<Item = impl AsRef<Utf8Path>>,
    ) -> Result<PackageQuery<'_>, Error> {
        let workspace = self.workspace();
        let package_ixs = paths
            .into_iter()
            .map(|path| {
                workspace
                    .member_by_path(path.as_ref())
                    .map(|package| package.package_ix())
            })
            .collect::<Result<SortedSet<_>, Error>>()?;

        Ok(self.query_from_parts(package_ixs, DependencyDirection::Forward))
    }

    /// Creates a new forward query over the specified workspace packages by name.
    ///
    /// This is similar to `cargo`'s `--package` option.
    ///
    /// Returns an error if any package names were unknown.
    pub fn query_workspace_names(
        &self,
        names: impl IntoIterator<Item = impl AsRef<str>>,
    ) -> Result<PackageQuery<'_>, Error> {
        let workspace = self.workspace();
        let package_ixs = names
            .into_iter()
            .map(|name| {
                workspace
                    .member_by_name(name.as_ref())
                    .map(|package| package.package_ix())
            })
            .collect::<Result<SortedSet<_>, Error>>()?;

        Ok(self.query_from_parts(package_ixs, DependencyDirection::Forward))
    }

    /// Creates a new query that returns transitive dependencies of the given packages in the
    /// specified direction.
    ///
    /// Returns an error if any package IDs are unknown.
    pub fn query_directed<'g, 'a>(
        &'g self,
        package_ids: impl IntoIterator<Item = &'a PackageId>,
        dep_direction: DependencyDirection,
    ) -> Result<PackageQuery<'g>, Error> {
        match dep_direction {
            DependencyDirection::Forward => self.query_forward(package_ids),
            DependencyDirection::Reverse => self.query_reverse(package_ids),
        }
    }

    /// Creates a new query that returns transitive dependencies of the given packages.
    ///
    /// Returns an error if any package IDs are unknown.
    pub fn query_forward<'g, 'a>(
        &'g self,
        package_ids: impl IntoIterator<Item = &'a PackageId>,
    ) -> Result<PackageQuery<'g>, Error> {
        Ok(PackageQuery {
            graph: self,
            params: QueryParams::Forward(self.package_ixs(package_ids)?),
        })
    }

    /// Creates a new query that returns transitive reverse dependencies of the given packages.
    ///
    /// Returns an error if any package IDs are unknown.
    pub fn query_reverse<'g, 'a>(
        &'g self,
        package_ids: impl IntoIterator<Item = &'a PackageId>,
    ) -> Result<PackageQuery<'g>, Error> {
        Ok(PackageQuery {
            graph: self,
            params: QueryParams::Reverse(self.package_ixs(package_ids)?),
        })
    }

    pub(super) fn query_from_parts(
        &self,
        package_ixs: SortedSet<NodeIndex<PackageIx>>,
        direction: DependencyDirection,
    ) -> PackageQuery<'_> {
        let params = match direction {
            DependencyDirection::Forward => QueryParams::Forward(package_ixs),
            DependencyDirection::Reverse => QueryParams::Reverse(package_ixs),
        };
        PackageQuery {
            graph: self,
            params,
        }
    }
}

impl<'g> PackageQuery<'g> {
    /// Returns the package graph on which the query is going to be executed.
    pub fn graph(&self) -> &'g PackageGraph {
        self.graph
    }

    /// Returns the direction the query is happening in.
    pub fn direction(&self) -> DependencyDirection {
        self.params.direction()
    }

    /// Returns the list of initial packages specified in the query.
    ///
    /// The order of packages is unspecified.
    pub fn initials<'a>(&'a self) -> impl ExactSizeIterator<Item = PackageMetadata<'g>> + 'a {
        let graph = self.graph;
        self.params.initials().iter().map(move |package_ix| {
            graph
                .metadata(&graph.dep_graph[*package_ix])
                .expect("valid ID")
        })
    }

    /// Returns true if the query starts from the given package ID.
    ///
    /// Returns an error if this package ID is unknown.
    pub fn starts_from(&self, package_id: &PackageId) -> Result<bool, Error> {
        Ok(self.params.has_initial(self.graph.package_ix(package_id)?))
    }

    /// Converts this `PackageQuery` into a `FeatureQuery`, using the given feature filter.
    ///
    /// This will cause the feature graph to be constructed if it hasn't been done so already.
    pub fn to_feature_query(&self, filter: impl FeatureFilter<'g>) -> FeatureQuery<'g> {
        let package_ixs = self.params.initials();
        let feature_graph = self.graph.feature_graph();
        let feature_ixs =
            feature_graph.feature_ixs_for_package_ixs_filtered(package_ixs.iter().copied(), filter);
        feature_graph.query_from_parts(feature_ixs, self.direction())
    }

    /// Resolves this query into a set of known packages, following every link found along the
    /// way.
    ///
    /// This is the entry point for iterators.
    pub fn resolve(self) -> PackageSet<'g> {
        PackageSet::new(self)
    }

    /// Resolves this query into a set of known packages, using the provided resolver to
    /// determine which links are followed.
    pub fn resolve_with(self, resolver: impl PackageResolver<'g>) -> PackageSet<'g> {
        PackageSet::with_resolver(self, resolver)
    }

    /// Resolves this query into a set of known packages, using the provided resolver function
    /// to determine which links are followed.
    pub fn resolve_with_fn(
        self,
        resolver_fn: impl FnMut(&PackageQuery<'g>, PackageLink<'g>) -> bool,
    ) -> PackageSet<'g> {
        self.resolve_with(ResolverFn(resolver_fn))
    }
}
