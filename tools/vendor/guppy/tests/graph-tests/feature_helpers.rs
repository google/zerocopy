// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use guppy::{
    PackageId,
    graph::feature::{FeatureLabel, FeatureSet},
};

pub(super) fn assert_features_for_package(
    feature_set: &FeatureSet<'_>,
    package_id: &PackageId,
    expected: Option<&[FeatureLabel<'_>]>,
    msg: &str,
) {
    let actual = feature_set
        .features_for(package_id)
        .expect("valid package ID");

    assert_eq!(
        actual.as_ref().map(|list| list.labels()),
        expected,
        "{msg}: for package {package_id}, features in feature set match"
    );
}
