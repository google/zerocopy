// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Support for weak features.

use crate::graph::{
    PackageIx,
    feature::{ConditionalLink, FeatureEdgeReference},
};
use indexmap::IndexSet;
use itertools::Either;
use petgraph::graph::EdgeIndex;
use smallvec::SmallVec;

/// Data structure that tracks pairs of package indexes that form weak dependencies.
#[derive(Clone, Debug)]
pub(super) struct WeakDependencies {
    ixs: IndexSet<EdgeIndex<PackageIx>>,
}

impl WeakDependencies {
    pub(super) fn new() -> Self {
        Self {
            ixs: IndexSet::new(),
        }
    }

    pub(super) fn insert(&mut self, edge_ix: EdgeIndex<PackageIx>) -> WeakIndex {
        WeakIndex(self.ixs.insert_full(edge_ix).0)
    }

    pub(super) fn get(&self, edge_ix: EdgeIndex<PackageIx>) -> Option<WeakIndex> {
        self.ixs.get_index_of(&edge_ix).map(WeakIndex)
    }

    #[inline]
    pub(super) fn new_buffer_states<'g, F>(&self, accept_fn: F) -> WeakBufferStates<'g, '_, F>
    where
        F: FnMut(ConditionalLink<'g>) -> bool,
    {
        WeakBufferStates::new(self, self.ixs.len(), accept_fn)
    }
}

// Not part of the public API -- exposed for testing.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
#[doc(hidden)]
pub struct WeakIndex(pub(super) usize);

/// Buffer states for weak indexes, to be used during a feature resolver traversal.
pub(super) struct WeakBufferStates<'g, 'a, F> {
    deps: &'a WeakDependencies,
    states: SmallVec<[SingleBufferState<'g>; 8]>,
    accept_fn: F,
}

impl<'g, 'a, F> WeakBufferStates<'g, 'a, F>
where
    F: FnMut(ConditionalLink<'g>) -> bool,
{
    #[inline]
    fn new(deps: &'a WeakDependencies, len: usize, accept_fn: F) -> Self {
        let mut states = SmallVec::with_capacity(len);
        states.resize_with(len, Default::default);
        Self {
            deps,
            states,
            accept_fn,
        }
    }

    pub(super) fn track(
        &mut self,
        edge_ref: FeatureEdgeReference<'g>,
        link: ConditionalLink<'g>,
        weak_index: Option<WeakIndex>,
    ) -> Either<Option<FeatureEdgeReference<'g>>, Vec<FeatureEdgeReference<'g>>> {
        match weak_index {
            Some(index) => {
                match &mut self.states[index.0] {
                    SingleBufferState::Buffered(buffer) => {
                        // Package not currently accepted -- add to the buffer.
                        buffer.push((link, edge_ref));
                        Either::Left(None)
                    }
                    SingleBufferState::Accepted => {
                        // Weak link, but package already accepted.
                        Either::Left((self.accept_fn)(link).then_some(edge_ref))
                    }
                }
            }
            None => {
                if !(self.accept_fn)(link) {
                    // This link was not accepted -- ignore its presence.
                    return Either::Left(None);
                }

                match self.deps.get(link.package_edge_ix()) {
                    Some(weak_index) => {
                        match std::mem::replace(
                            &mut self.states[weak_index.0],
                            SingleBufferState::Accepted,
                        ) {
                            SingleBufferState::Buffered(buffer) => {
                                // Transition from buffered to accepted.
                                let mut edge_refs: Vec<_> = buffer
                                    .into_iter()
                                    .filter_map(|(link, edge_ref)| {
                                        // Filter buffered links.
                                        (self.accept_fn)(link).then_some(edge_ref)
                                    })
                                    .collect();
                                edge_refs.push(edge_ref);
                                Either::Right(edge_refs)
                            }
                            SingleBufferState::Accepted => {
                                // Weak link, but package already accepted.
                                Either::Left(Some(edge_ref))
                            }
                        }
                    }
                    None => {
                        // Not a weak link.
                        Either::Left(Some(edge_ref))
                    }
                }
            }
        }
    }
}

/// Buffer state for a single weak index in an in-progress resolver.
pub(super) enum SingleBufferState<'g> {
    Buffered(SingleBufferVec<'g>),
    Accepted,
}

impl Default for SingleBufferState<'_> {
    fn default() -> Self {
        Self::Buffered(SingleBufferVec::new())
    }
}

type SingleBufferVec<'g> = Vec<(ConditionalLink<'g>, FeatureEdgeReference<'g>)>;
