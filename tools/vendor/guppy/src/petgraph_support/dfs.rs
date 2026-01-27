// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use petgraph::{
    prelude::*,
    visit::{
        DfsPostOrder, IntoEdgeReferences, IntoEdges, IntoEdgesDirected, Reversed,
        ReversedEdgeReference, VisitMap,
    },
};

/// `DfsPostOrder::next`, adapted for a buffered filter that's also FnMut.
pub fn dfs_next_buffered_filter<N, VM, G>(
    dfs: &mut DfsPostOrder<N, VM>,
    graph: G,
    mut buffered_filter: impl BufferedEdgeFilter<G>,
) -> Option<N>
where
    N: Copy + PartialEq,
    VM: VisitMap<N>,
    G: IntoEdges<NodeId = N>,
{
    // Adapted from DfsPostOrder::next in petgraph 0.5.0.
    while let Some(&nx) = dfs.stack.last() {
        if dfs.discovered.visit(nx) {
            // First time visiting `nx`: Push neighbors, don't pop `nx`
            let neighbors = graph.edges(nx).flat_map(|edge| {
                buffered_filter
                    .filter(edge)
                    .into_iter()
                    .map(|edge| edge.target())
            });
            for succ in neighbors {
                if !dfs.discovered.is_visited(&succ) {
                    dfs.stack.push(succ);
                }
            }
        } else {
            dfs.stack.pop();
            if dfs.finished.visit(nx) {
                // Second time: All reachable nodes must have been finished
                return Some(nx);
            }
        }
    }
    None
}

/// A buffered filter is a graph traversal edge filter that can buffer up some edges to be
/// returned later.
pub trait BufferedEdgeFilter<G>
where
    G: IntoEdges,
{
    /// Returns a list of edge references to follow.
    type Iter: IntoIterator<Item = G::EdgeRef>;

    fn filter(&mut self, edge: G::EdgeRef) -> Self::Iter;
}

impl<G, T> BufferedEdgeFilter<G> for &mut T
where
    T: BufferedEdgeFilter<G>,
    G: IntoEdges,
{
    /// Returns a list of node IDs to follow.
    type Iter = T::Iter;

    #[inline]
    fn filter(&mut self, edge: G::EdgeRef) -> Self::Iter {
        (*self).filter(edge)
    }
}

#[derive(Debug)]
pub struct SimpleEdgeFilterFn<F>(pub F);

impl<F, G> BufferedEdgeFilter<G> for SimpleEdgeFilterFn<F>
where
    F: FnMut(G::EdgeRef) -> bool,
    G: IntoEdges,
{
    type Iter = Option<G::EdgeRef>;

    #[inline]
    fn filter(&mut self, edge: G::EdgeRef) -> Self::Iter {
        if (self.0)(edge) { Some(edge) } else { None }
    }
}

#[derive(Debug)]
pub struct BufferedEdgeFilterFn<F>(pub F);

impl<F, G, I> BufferedEdgeFilter<G> for BufferedEdgeFilterFn<F>
where
    F: FnMut(G::EdgeRef) -> I,
    G: IntoEdges,
    I: IntoIterator<Item = G::EdgeRef>,
{
    type Iter = I;

    #[inline]
    fn filter(&mut self, edge: G::EdgeRef) -> Self::Iter {
        (self.0)(edge)
    }
}

#[derive(Debug)]
pub struct ReversedBufferedFilter<T>(pub T);

impl<T, G> BufferedEdgeFilter<Reversed<G>> for ReversedBufferedFilter<T>
where
    T: BufferedEdgeFilter<G>,
    G: IntoEdgesDirected,
{
    type Iter =
        ReversedEdgeReferences<<<T as BufferedEdgeFilter<G>>::Iter as IntoIterator>::IntoIter>;

    fn filter(&mut self, edge: <Reversed<G> as IntoEdgeReferences>::EdgeRef) -> Self::Iter {
        ReversedEdgeReferences {
            iter: self.0.filter(edge.into_unreversed()).into_iter(),
        }
    }
}

// TODO: replace with upstream impl
pub struct ReversedEdgeReferences<I> {
    iter: I,
}

impl<I> Iterator for ReversedEdgeReferences<I>
where
    I: Iterator,
{
    type Item = ReversedEdgeReference<I::Item>;

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        // Ugh this sucks! Should be supported upstream.
        // SAFETY: this is just a newtype. This is SUCH a horrible hack.
        let item = self.iter.next()?;
        Some(unsafe { horrible_transmute::<I::Item, ReversedEdgeReference<I::Item>>(item) })
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

unsafe fn horrible_transmute<A, B>(a: A) -> B {
    unsafe {
        let b = ::core::ptr::read(&a as *const A as *const B);
        ::core::mem::forget(a);
        b
    }
}

// Check that the above transmute is actually safe.
static_assertions::assert_eq_size!((), ReversedEdgeReference<()>);
