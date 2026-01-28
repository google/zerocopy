// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::graph::{
    feature::{FeatureGraph, FeatureId, FeatureSet},
    fixedbitset_strategy,
};
use petgraph::prelude::*;
use proptest::prelude::*;

/// ## Helpers for property testing
///
/// The methods in this section allow a `FeatureGraph` to be used in property-based testing
/// scenarios.
///
/// Currently, [proptest 1](https://docs.rs/proptest/1) is supported if the `proptest1`
/// feature is enabled.
impl<'g> FeatureGraph<'g> {
    /// Returns a `Strategy` that generates random feature IDs from this graph.
    ///
    /// The IDs so chosen are uniformly random from the entire feature graph. In other words, a
    /// package with more optional features is more likely to be chosen.
    ///
    /// Requires the `proptest1` feature to be enabled.
    ///
    /// ## Panics
    ///
    /// Panics if there are no packages in the `PackageGraph` from which this `FeatureGraph` was
    /// derived.
    pub fn proptest1_id_strategy(&self) -> impl Strategy<Value = FeatureId<'g>> + 'g + use<'g> {
        let dep_graph = self.dep_graph();
        let package_graph = self.package_graph;
        any::<prop::sample::Index>().prop_map(move |index| {
            let feature_ix = NodeIndex::new(index.index(dep_graph.node_count()));
            FeatureId::from_node(package_graph, &dep_graph[feature_ix])
        })
    }

    /// Returns a `Strategy` that generates random feature sets from this graph.
    pub fn proptest1_set_strategy(&self) -> impl Strategy<Value = FeatureSet<'g>> + 'g + use<'g> {
        let this = *self;
        fixedbitset_strategy(self.feature_count())
            .prop_map(move |included| FeatureSet::from_included(this, included))
    }
}
