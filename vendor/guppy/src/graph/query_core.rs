// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::{
    graph::{DependencyDirection, GraphSpec},
    petgraph_support::dfs::{BufferedEdgeFilter, dfs_next_buffered_filter},
    sorted_set::SortedSet,
};
use fixedbitset::FixedBitSet;
use petgraph::{
    graph::IndexType,
    prelude::*,
    visit::{IntoEdges, IntoNeighbors, Visitable},
};
use std::fmt;

pub(super) enum QueryParams<G: GraphSpec> {
    Forward(SortedSet<NodeIndex<G::Ix>>),
    Reverse(SortedSet<NodeIndex<G::Ix>>),
}

impl<G: GraphSpec> QueryParams<G> {
    pub(super) fn direction(&self) -> DependencyDirection {
        match self {
            QueryParams::Forward(_) => DependencyDirection::Forward,
            QueryParams::Reverse(_) => DependencyDirection::Reverse,
        }
    }

    /// Returns true if this query specifies this package as an initial.
    pub(super) fn has_initial(&self, initial: NodeIndex<G::Ix>) -> bool {
        match self {
            QueryParams::Forward(v) => v.contains(&initial),
            QueryParams::Reverse(v) => v.contains(&initial),
        }
    }

    pub(super) fn initials(&self) -> &[NodeIndex<G::Ix>] {
        match self {
            QueryParams::Forward(v) => v,
            QueryParams::Reverse(v) => v,
        }
    }
}

impl<G: GraphSpec> Clone for QueryParams<G>
where
    G::Ix: Clone,
{
    fn clone(&self) -> Self {
        match self {
            QueryParams::Forward(v) => QueryParams::Forward(v.clone()),
            QueryParams::Reverse(v) => QueryParams::Reverse(v.clone()),
        }
    }
}

impl<G: GraphSpec> fmt::Debug for QueryParams<G>
where
    G::Ix: fmt::Debug,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            QueryParams::Forward(v) => f.debug_tuple("Forward").field(v).finish(),
            QueryParams::Reverse(v) => f.debug_tuple("Reverse").field(v).finish(),
        }
    }
}

pub(super) fn all_visit_map<G, Ix>(graph: G) -> (FixedBitSet, usize)
where
    G: Visitable<NodeId = NodeIndex<Ix>, Map = FixedBitSet>,
    Ix: IndexType,
{
    let mut visit_map = graph.visit_map();
    // Mark all nodes visited.
    visit_map.insert_range(..);
    let len = visit_map.len();
    (visit_map, len)
}

pub(super) fn reachable_map<G, Ix>(
    graph: G,
    roots: impl Into<Vec<G::NodeId>>,
) -> (FixedBitSet, usize)
where
    G: Visitable<NodeId = NodeIndex<Ix>, Map = FixedBitSet> + IntoNeighbors,
    Ix: IndexType,
{
    // To figure out what nodes are reachable, run a DFS starting from the roots.
    // This is DfsPostOrder since that handles cycles while a regular DFS doesn't.
    let mut dfs = DfsPostOrder::empty(graph);
    dfs.stack = roots.into();
    while dfs.next(graph).is_some() {}

    // Once the DFS is done, the discovered map (or the finished map) is what's reachable.
    debug_assert_eq!(
        dfs.discovered, dfs.finished,
        "discovered and finished maps match at the end"
    );
    let reachable = dfs.discovered;
    let len = reachable.count_ones(..);
    (reachable, len)
}

pub(super) fn reachable_map_buffered_filter<G, Ix>(
    graph: G,
    mut filter: impl BufferedEdgeFilter<G>,
    roots: impl Into<Vec<G::NodeId>>,
) -> (FixedBitSet, usize)
where
    G: Visitable<NodeId = NodeIndex<Ix>, Map = FixedBitSet> + IntoEdges,
    Ix: IndexType,
{
    // To figure out what nodes are reachable, run a DFS starting from the roots.
    // This is DfsPostOrder since that handles cycles while a regular DFS doesn't.
    let mut dfs = DfsPostOrder::empty(graph);
    dfs.stack = roots.into();
    while dfs_next_buffered_filter(&mut dfs, graph, &mut filter).is_some() {}

    // Once the DFS is done, the discovered map (or the finished map) is what's reachable.
    debug_assert_eq!(
        dfs.discovered, dfs.finished,
        "discovered and finished maps match at the end"
    );
    let reachable = dfs.discovered;
    let len = reachable.count_ones(..);
    (reachable, len)
}
