// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Print out direct and transitive dependencies of a package.

use guppy::{CargoMetadata, Error, PackageId, graph::DependencyDirection};
use std::iter;

fn main() -> Result<(), Error> {
    // `guppy` accepts `cargo metadata` JSON output. Use a pre-existing fixture for these examples.
    let metadata = CargoMetadata::parse_json(include_str!("../../fixtures/small/metadata1.json"))?;
    let package_graph = metadata.build_graph()?;

    // `guppy` provides several ways to get hold of package IDs. Use a pre-defined one for this
    // example.
    let package_id = PackageId::new("testcrate 0.1.0 (path+file:///fakepath/testcrate)");

    // The `metadata` method returns information about the package, or `None` if the package ID
    // wasn't recognized.
    let package = package_graph.metadata(&package_id).unwrap();

    // `direct_links` returns all direct dependencies of a package.
    for link in package.direct_links() {
        // A dependency link contains `from`, `to` and `edge`. The edge has information about e.g.
        // whether this is a build dependency.
        println!("direct: {}", link.to().id());
    }

    // Transitive dependencies are obtained through the `query_` APIs. They are always presented in
    // topological order.
    let query = package_graph.query_forward(iter::once(&package_id))?;
    let package_set = query.resolve();
    for dep_id in package_set.package_ids(DependencyDirection::Forward) {
        // PackageSet also has an `links()` method which returns links instead of package IDs.
        println!("transitive: {dep_id}");
    }
    Ok(())
}
