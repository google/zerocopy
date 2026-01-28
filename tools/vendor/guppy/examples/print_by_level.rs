// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Print out dependencies of a graph, level by level.
//!
//! This example will print out duplicate dependencies if they show up at multiple levels. If you
//! don't want that, you can maintain a 'seen' set.

use guppy::{CargoMetadata, Error};
use std::{
    collections::BTreeMap,
    io::{Write, stdout},
};

fn main() -> Result<(), Error> {
    // `guppy` accepts `cargo metadata` JSON output. Use a pre-existing fixture for these examples.
    let metadata =
        CargoMetadata::parse_json(include_str!("../../fixtures/large/metadata_libra.json"))?;
    let package_graph = metadata.build_graph()?;

    // Pick an interesting package to compute dependencies of.
    let vm_metadata = package_graph
        .workspace()
        .member_by_path("language/vm/vm-runtime")
        .expect("known workspace path");

    // Use a BTreeMap to deduplicate dependencies within a level below while keeping package IDs
    // ordered.
    let mut current = BTreeMap::new();
    current.insert(vm_metadata.id(), vm_metadata);

    let mut level = 0;

    // One could use println! directly at the cost of a lot of unnecessary lock and unlock actions.
    // Grabbing the lock once is more efficient.
    let stdout = stdout();
    let mut f = stdout.lock();

    // Keep iterating over package IDs until no more remain.
    while !current.is_empty() {
        // Print out details for this level.
        writeln!(f, "level {level}:").unwrap();
        for (id, metadata) in &current {
            writeln!(f, "* {}: {}", id, metadata.name()).unwrap();
        }
        writeln!(f).unwrap();
        level += 1;

        // Compute the package IDs in the next level.
        let next: BTreeMap<_, _> = current
            .into_iter()
            .flat_map(|(id, _)| {
                // This is a flat_map because each package in current has multiple dependencies, and
                // we want to collect all of them together.
                let links = package_graph.metadata(id).expect("valid ID").direct_links();
                links.map(|link| {
                    let to = link.to();
                    // Since we're iterating over transitive dependencies, we use the 'to' ID here.
                    // If we were iterating over transitive reverse deps, we'd use the 'from' ID.
                    (to.id(), to)
                })
            })
            .collect();

        current = next;
    }

    Ok(())
}
