// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use crate::petgraph_support::edge_triple;
use petgraph::visit::{IntoEdges, VisitMap, Visitable, Walker};
use std::iter;

#[derive(Clone, Debug)]
pub(crate) struct EdgeDfs<E, N, VM> {
    /// The queue of (source, target, edge) to visit.
    pub stack: Vec<(N, N, E)>,
    /// The map of discovered nodes
    pub discovered: VM,
}

impl<E, N, VM> EdgeDfs<E, N, VM>
where
    E: Copy + PartialEq,
    N: Copy + PartialEq,
    VM: VisitMap<N>,
{
    /// Creates a new EdgeDfs, using the graph's visitor map, and puts all edges out of `initials`
    /// in the queue of edges to visit.
    pub(crate) fn new<G>(graph: G, initials: impl IntoIterator<Item = N>) -> Self
    where
        G: Visitable<Map = VM> + IntoEdges<NodeId = N, EdgeId = E>,
    {
        let mut discovered = graph.visit_map();
        let stack = initials
            .into_iter()
            .filter_map(|node_ix| {
                // This check ensures that if a node is repeated in initials, its edges are only
                // added once.
                if discovered.visit(node_ix) {
                    Some(graph.edges(node_ix).map(edge_triple))
                } else {
                    None
                }
            })
            .flatten()
            .collect();
        Self { stack, discovered }
    }

    /// Creates a new EdgeDfs, using the graph's visitor map, and puts all edges out of `start`
    /// in the queue of edges to visit.
    #[allow(dead_code)]
    pub(crate) fn new_single<G>(graph: G, start: N) -> Self
    where
        G: Visitable<Map = VM> + IntoEdges<NodeId = N, EdgeId = E>,
    {
        Self::new(graph, iter::once(start))
    }

    /// Returns the next edge in the dfs, or `None` if no more edges remain.
    pub fn next<G>(&mut self, graph: G) -> Option<(N, N, E)>
    where
        G: IntoEdges<NodeId = N, EdgeId = E>,
    {
        let (source, target, edge) = self.stack.pop()?;
        if self.discovered.visit(target) {
            self.stack.extend(graph.edges(target).map(edge_triple));
        }
        Some((source, target, edge))
    }
}

impl<G> Walker<G> for EdgeDfs<G::EdgeId, G::NodeId, G::Map>
where
    G: IntoEdges + Visitable,
{
    type Item = (G::NodeId, G::NodeId, G::EdgeId);

    fn walk_next(&mut self, context: G) -> Option<Self::Item> {
        self.next(context)
    }
}
