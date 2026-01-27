// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use petgraph::{
    graph::{EdgeReference, IndexType},
    prelude::*,
    visit::ReversedEdgeReference,
};

/// Provides a way to obtain graph::EdgeReference instances from arbitrary EdgeRef ones.
pub trait GraphEdgeRef<'a, E, Ix: IndexType>: EdgeRef {
    fn into_edge_reference(self) -> EdgeReference<'a, E, Ix>;
}

impl<'a, E, Ix: IndexType> GraphEdgeRef<'a, E, Ix> for EdgeReference<'a, E, Ix> {
    fn into_edge_reference(self) -> EdgeReference<'a, E, Ix> {
        self
    }
}

impl<'a, E, Ix: IndexType> GraphEdgeRef<'a, E, Ix>
    for ReversedEdgeReference<EdgeReference<'a, E, Ix>>
{
    fn into_edge_reference(self) -> EdgeReference<'a, E, Ix> {
        self.into_unreversed()
    }
}
