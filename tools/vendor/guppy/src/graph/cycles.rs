// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Code for handling cycles in dependency graphs.
//!
//! See [`Cycles`][] for detailed docs.

use crate::{
    Error, PackageId,
    graph::{PackageGraph, PackageIx},
    petgraph_support::scc::Sccs,
};

/// Contains information about dependency cycles.
///
/// More accurately, information about Strongly Connected Components with 2 or more elements.
/// Constructed through `PackageGraph::cycles`.
///
/// This page includes a bunch of detailed information on cycles, but here's the TLDR:
///
/// * Yes, cycles can happen
/// * Cycles only happen with dev-dependencies
/// * These cycles have properties that make them easy to handle
/// * We handle this in APIs like [`PackageSet::packages`][`crate::graph::PackageSet::packages`]
/// * As a result, you probably don't actually need this module
///
/// The slighly more detailed summary is that any graph of "packages" is conflating
/// the "real" package with its tests, which are actually separate binaries. These
/// tests *always* depend on the "real" package, and if we bothered to encode that
/// then any package with tests would have a cyclic dependency on itself -- so we
/// don't encode that. Unfortunately dev-dependencies allow tests to *indirectly*
/// depend on the "real" package, creating a cycle you *do* see.
///
/// If you only care about "real" builds, you can simply ignore the dev-dependency
/// edges and restore a nice and simple DAG that can be topologically sorted. This is what
/// we do for you in APIs like [`PackageSet::packages`][`crate::graph::PackageSet::packages`].
///
/// If you care about tests and dev-dependencies, we recommend treating those as
/// different from the "real" ones (essentially desugarring the package into two nodes).
/// Because all dev builds are roots of the package graph (nothing depends on a test/benchmark),
/// they can always go at the start/end (depending on direction) of the topological sort.
/// This means you can just do add a second loop before/after the "real" one.
///
/// For instance, here's a simple program that recursively computes some property of packages
/// (here "whether serde is a transitive dependency"):
///
/// ```
/// use guppy::{CargoMetadata, graph::DependencyDirection};
/// use std::collections::HashMap;
///
/// let metadata = CargoMetadata::parse_json(include_str!("../../../fixtures/small/metadata1.json")).unwrap();
/// let package_graph = metadata.build_graph().unwrap();
/// let workspace_members = package_graph.resolve_workspace();
/// let dependency_graph = package_graph.query_workspace().resolve();
///
/// // Whether the "real" package uses serde
/// let mut package_uses_serde = HashMap::new();
/// // Whether the "dev" package uses serde
/// let mut dev_package_uses_serde = HashMap::new();
///
/// // Iterate over packages in reverse topo order (process dependencies first)
/// for package in dependency_graph.packages(DependencyDirection::Reverse) {
///     // A package uses serde if...
///     let uses_serde = if package.name() == "serde" {
///         // It is literally serde (base case)
///         true
///     } else {
///         // It has a non-dev-dependency on a package which uses serde
///         // (dev-dependencies handled in the second loop)
///         package.direct_links().any(|link| {
///             !link.dev_only() && package_uses_serde[link.to().id()]
///         })
///     };
///     // Record this package's result
///     package_uses_serde.insert(package.id(), uses_serde);
/// }
///
/// // Now iterate over the workspace members to handle their tests (if any)
/// // Note that DependencyDirection doesn't matter here, we're literally
/// // just looping over every workspace member in arbitrary order!
/// for package in workspace_members.packages(DependencyDirection::Reverse) {
///     // Check dev-packages using the "real" package results for all links!
///     let uses_serde = package.direct_links().any(|link| {
///         package_uses_serde[link.to().id()]
///     });
///     // Record this dev-package's result
///     dev_package_uses_serde.insert(package.id(), uses_serde);
/// }
///
/// // Now we have all the values computed!
/// for (id, &uses_serde) in &package_uses_serde {
///     if uses_serde {
///         let name = package_graph.metadata(id).unwrap().name();
///         println!("{name} uses serde!");
///     }
/// }
/// for (id, &uses_serde) in &dev_package_uses_serde {
///     if uses_serde {
///         let name = package_graph.metadata(id).unwrap().name();
///         println!("{name}'s tests use serde!");
///     }
/// }
/// ```
///
///
///
///
///
/// # Why Cargo Dependency Graphs Have Cycles
///
/// Dependency graphs are generally Directed Acyclic Graphs (DAGs), where each package
/// is a node and each dependency is an edge. These graphs are acyclic (contain no cycles)
/// because anything else would be a paradox -- how do you build X if it depends on itself?
/// You don't!
///
/// So why does this API exist? It wouldn't make sense for Cargo to have cycles!
///
/// The problem is that "the Cargo dependency graph" is actually two different graphs
/// at different levels of abstraction: The Package Graph (Guppy, cargo-metadata), and
/// The Build Graph (Cargo's internals). These two graphs are different because each
/// package is actually a bunch of different
/// [build targets in a trenchcoat][`crate::graph::PackageMetadata::build_targets`] -- libs,
/// bins, tests, benches, and so on. In The Build Graph these different build targets get
/// their own nodes. In The Package Graph all those targets gets merged together into one
/// big node. The Build Graph is always a proper DAG, but The Package Graph can have cycles.
///
/// Thankfully these cycles can only be created by one specific (and rare) situation:
/// dev-dependencies. **A test/bench target for a package is allowed to indirectly
/// depend on the same package's lib/bin target, and this creates apparent cycles
/// in the package graph!** That's it!
///
/// As we'll see, **simply ignoring all dev-dependency edges eliminates all cycles
/// *and* preserves the ordering constraints of the dependency graph.**
///
///
///
/// # An Example Cyclic Workspace
///
/// As a concrete example, consider [the serde workspace][serde_github], which
/// actually has this "problem": there's a "cycle" between serde and serde_derive.
/// In normal builds this cycle doesn't exist: serde_derive is actually a standalone
/// crate, while [serde (optionally) pulls in serde_derive as a dependency][serde_toml].
/// The "cycle" only appears when testing serde_derive: [serde_derive's tests quite
/// reasonably depend on serde][serde_derive_toml] to test the proc-macro's output,
/// creating a cycle!
///
/// The way to resolve this monstrosity is to realize that the tests for serde_derive
/// are actually a completely different binary from the serde_derive *library*. Let's
/// call those tests serde_derive_dev. So although the (Package) graph reported by Guppy
/// (and cargo-metadata) looks like a cycle:
///
/// ```text
/// serde <-----+
///   |         |
///   |         |
///   +--> serde_derive
/// ```
///
/// In actuality, serde_derive_dev breaks the cycle and creates a nice clean DAG
/// (in The Build Graph):
///
/// ```text
///   +-- serde_derive_dev
///   |          |
///   v          |
/// serde        |
///   |          |
///   |          v
///   +---> serde_derive
/// ```
///
/// Here's the really important thing to notice: serde_derive_dev is actually a *root*
/// in The Build Graph, and this is always true! Nothing should ever depend on the *tests*
/// or *benchmarks* for another library.
///
/// This is the key insight to ignoring dev-dependency edges. As we'll see, the roots
/// (and leaves) of a DAG are in some sense "ignorable" by the rest of the graph,
/// because they can't change the ordering constraints between other packages.
///
///
///
/// # Topological Sort Is Great (And Composable)
///
/// Now that we understand *why* cycles can happen in the package graph, let's look at
/// what those cycles mess up, and how to deal with them.
///
/// One of the big reasons everyone loves DAGs is because you can get a Topological
/// Sort of them. Topological Sort
/// (with [`DependencyDirection::Forward`][`crate::graph::DependencyDirection::Forward`])
/// is just a fancy way of saying "a list where packages always appear before their dependencies"
/// (vice-versa for [`DependencyDirection::Reverse`][`crate::graph::DependencyDirection::Reverse`]).
///
/// This is really convenient! If you need to do things in "dependency order" you can just
/// topologically sort the packages and then boring old for-loops will magically get
/// everything done before it's needed.
///
/// Unfortunately, you can't get the Topological Sort of a graph with cycles because that
/// doesn't make sense. And yet, Guppy has
/// [several APIs which do exactly that][`crate::graph::PackageSet::packages`].
/// What gives? The docs say:
///
/// > The packages within a dependency cycle will be returned in non-dev order. When the
/// > direction is forward, if package Foo has a dependency on Bar, and Bar has a cyclic
/// > dev-dependency on Foo, then Foo is returned before Bar.
///
/// We just ignore the dev-dependency edges! Problem Solved.
///
/// But isn't this throwing out important information that could change the result? Nope!
///
/// As we saw in the previous section, all dev-builds are roots in The Build Graph.
/// Ignoring all dev-dependency edges is equivalent to deleting all of those roots.
/// This may "orphan" dependencies that are only used for dev-builds, but we still
/// keep them in the graph and properly include them in the sort.
///
/// As it turns out, you can recursively compute the topological sort of a graph as follows:
///
/// 1. delete a root (or leaf)
/// 2. compute the topological sort of the new graph
/// 3. append the root (or leaf) to the start (or end) of the list
///
/// **Even although we delete all the dev-nodes from the graph when doing our sort,
/// if you want to "add them back" the only thing you need to do is handle them before
/// (or after) everything else!** Even better: all the dev-builds are roots at the same
/// time, so you can process them in any order!
///
/// Just remember that every node with dev-dependencies is really two nodes: the "normal"
/// version without dev-dependencies, and the version with them. Exactly how you want
/// to express that notion in your code is up to you. (Two different loops is the simplest.)
///
///
///
///
/// # Reasoning About Cycles: Strongly Connected Components
///
/// Ok but wait, none of that involved Strongly Connected Components! Yeah, isn't that great? 😄
///
/// Oh you still want to "know" about the cycles? Then we've gotta bust out the heavy
/// general-purpose machinery. Thankfully the problem of cycles in directed graphs is
/// an old and well-studied problem with a conceptually simple solution: hide the cycle
/// in a box and pretend that it's just one Really Big Node in the DAG.
///
/// Yes, really, that's all that Strongly Connected Components are. More precisely, SCCs
/// are defined to be maximal sets of nodes such that "every node in an SCC can reach
/// every other node in that SCC" (a property which definitely holds for cycles).
/// The reason for this more complicated definition is that you can have a bunch of
/// cycles all knotted together in a nasty ball, and trying to tease out individual
/// cycles isn't really helpful. So we just wrap the whole ball of nodes up into one
/// big "I give up" box and forget about it!
///
/// Now, what does this get us?
///
/// The graph *between* Strongly Connected Components is *always* a DAG, so you can
/// always topologically sort *that*. In really nasty cases this is just vacuously
/// true (all the nodes end up in one SCC, and so the "Graph of SCCs" is just one big
/// unsorted node). On the other hand, if the graph already *is* a DAG then each node
/// is its own SCC, and so we lose nothing. In this way SCCs give us a way to preserve
/// all the *nice* parts of our graph while also isolating the problematic parts
/// (SCCs with more than 1 node) to something self-contained that we can handle specially.
///
/// In the general case, nothing more can be done to order an SCC. By definition every
/// node depends on every other node! But as we've seen in the previous section, there
/// actually *is* a good way to order packages even with cycles, and so we maintain
/// that ordering for our SCCs: it's just the topological sort with all the
/// dev-dependencies ignored.
///
///
///
///
/// [serde_github]: https://github.com/serde-rs/serde
/// [serde_toml]: https://github.com/serde-rs/serde/blob/072145e0e913df7686f001dbf29e43a0ff7afac4/serde/Cargo.toml#L17-L18
/// [serde_derive_toml]: https://github.com/serde-rs/serde/blob/072145e0e913df7686f001dbf29e43a0ff7afac4/serde_derive/Cargo.toml#L29-L30
pub struct Cycles<'g> {
    package_graph: &'g PackageGraph,
    sccs: &'g Sccs<PackageIx>,
}

impl<'g> Cycles<'g> {
    pub(super) fn new(package_graph: &'g PackageGraph) -> Self {
        Self {
            package_graph,
            sccs: package_graph.sccs(),
        }
    }

    /// Returns true if these two IDs are in the same cycle.
    ///
    /// This is equivalent to checking if they're in the same Strongly Connected Component.
    pub fn is_cyclic(&self, a: &PackageId, b: &PackageId) -> Result<bool, Error> {
        let a_ix = self.package_graph.package_ix(a)?;
        let b_ix = self.package_graph.package_ix(b)?;
        Ok(self.sccs.is_same_scc(a_ix, b_ix))
    }

    /// Returns all the Strongly Connected Components (SCCs) of 2 or more elements in this graph.
    ///
    /// SCCs are returned in topological order: if packages in SCC B depend on packages in SCC
    /// A, A is returned before B.
    ///
    /// Within an SCC, nodes are returned in non-dev order: if package Foo has a dependency on Bar,
    /// and Bar has a cyclic dev-dependency on Foo, then Foo is returned before Bar.
    ///
    /// See the type-level docs for details.
    pub fn all_cycles(&self) -> impl DoubleEndedIterator<Item = Vec<&'g PackageId>> + 'g + use<'g> {
        let dep_graph = &self.package_graph.dep_graph;
        self.sccs
            .multi_sccs()
            .map(move |scc| scc.iter().map(move |ix| &dep_graph[*ix]).collect())
    }
}
