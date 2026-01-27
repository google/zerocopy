// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Print out crates in a workspace in topological order.
//!
//! The into_iter_ids and into_iter_metadatas iterators return packages in topological order. Note
//! that into_iter_links returns links in "link order" -- see its documentation for more.

use guppy::{CargoMetadata, Error, graph::DependencyDirection};

fn main() -> Result<(), Error> {
    // `guppy` accepts `cargo metadata` JSON output. Use a pre-existing fixture for these examples.
    let metadata =
        CargoMetadata::parse_json(include_str!("../../fixtures/large/metadata_libra.json"))?;
    let package_graph = metadata.build_graph()?;

    // This produces the set of packages in this workspace.
    let workspace_set = package_graph.resolve_workspace();

    // Iterate over packages in forward topo order.
    for package in workspace_set.packages(DependencyDirection::Forward) {
        // All selected packages are in the workspace.
        let workspace_path = package
            .source()
            .workspace_path()
            .expect("packages in workspace should have workspace path");
        println!("{}: {}", package.name(), workspace_path);
    }

    Ok(())
}
