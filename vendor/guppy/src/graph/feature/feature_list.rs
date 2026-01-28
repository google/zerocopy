// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! A sorted, deduplicated list of features from a single package.

use crate::{
    PackageId,
    graph::{
        PackageMetadata,
        feature::{FeatureId, FeatureLabel},
    },
    sorted_set::SortedSet,
};
use std::{fmt, slice, vec};

/// A sorted, deduplicated list of features from a single package.
///
/// This provides a convenient way to query and print out lists of features.
///
/// Returned by methods on `FeatureSet`.
#[derive(Clone, Eq, PartialEq)]
pub struct FeatureList<'g> {
    package: PackageMetadata<'g>,
    labels: SortedSet<FeatureLabel<'g>>,
}

impl<'g> FeatureList<'g> {
    /// Creates a new `FeatureList` from a package and an iterator over feature labels.
    pub fn new(
        package: PackageMetadata<'g>,
        labels: impl IntoIterator<Item = FeatureLabel<'g>>,
    ) -> Self {
        Self {
            package,
            labels: labels.into_iter().collect(),
        }
    }

    /// Returns the package corresponding to this feature list.
    pub fn package(&self) -> &PackageMetadata<'g> {
        &self.package
    }

    /// Returns true if this feature list contains this feature label.
    pub fn contains(&self, label: FeatureLabel<'_>) -> bool {
        self.labels.contains(&label)
    }

    /// Returns true if this feature list contains the "base" feature.
    ///
    /// The "base" feature represents the package with no features enabled.
    #[inline]
    pub fn has_base(&self) -> bool {
        self.contains(FeatureLabel::Base)
    }

    /// Returns true if this feature list contains the specified named feature.
    #[inline]
    pub fn has_named_feature(&self, feature_name: &str) -> bool {
        self.contains(FeatureLabel::Named(feature_name))
    }

    /// Returns true if this feature list contains the specified optional dependency.
    #[inline]
    pub fn has_optional_dependency(&self, dep_name: &str) -> bool {
        self.contains(FeatureLabel::OptionalDependency(dep_name))
    }

    /// Returns the list of labels as a slice.
    ///
    /// This slice is guaranteed to be sorted and unique.
    pub fn labels(&self) -> &[FeatureLabel<'g>] {
        self.labels.as_slice()
    }

    /// Returns an iterator containing all named features.
    ///
    /// The iterator is guaranteed to be sorted and unique.
    pub fn named_features(&self) -> impl Iterator<Item = &'g str> + '_ {
        // XXX: binary search?
        self.labels.iter().filter_map(|label| match label {
            FeatureLabel::Named(feature_name) => Some(*feature_name),
            _ => None,
        })
    }

    /// Returns an iterator containing all optional dependencies.
    ///
    /// The iterator is guaranteed to be sorted and unique.
    pub fn optional_deps(&self) -> impl Iterator<Item = &'g str> + '_ {
        // XXX: binary search?
        self.labels.iter().filter_map(|label| match label {
            FeatureLabel::OptionalDependency(dep_name) => Some(*dep_name),
            _ => None,
        })
    }

    /// Returns a borrowed iterator over feature IDs.
    pub fn iter<'a>(&'a self) -> Iter<'g, 'a> {
        self.into_iter()
    }

    /// Returns a pretty-printer over the list of feature labels.
    pub fn display_features<'a>(&'a self) -> DisplayFeatures<'g, 'a> {
        DisplayFeatures(self.labels())
    }

    /// Returns a vector of feature labels.
    ///
    /// The vector is guaranteed to be sorted and unique.
    pub fn into_labels(self) -> Vec<FeatureLabel<'g>> {
        self.labels.into_inner().into_vec()
    }
}

impl fmt::Debug for FeatureList<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FeatureList")
            .field("package", self.package.id())
            .field("labels", &self.display_features())
            .finish()
    }
}

impl<'g> IntoIterator for FeatureList<'g> {
    type Item = FeatureId<'g>;
    type IntoIter = IntoIter<'g>;

    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<'a, 'g> IntoIterator for &'a FeatureList<'g> {
    type Item = FeatureId<'g>;
    type IntoIter = Iter<'g, 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Iter::new(self)
    }
}

/// An owned iterator over a `FeatureList`.
pub struct IntoIter<'g> {
    package_id: &'g PackageId,
    iter: vec::IntoIter<FeatureLabel<'g>>,
}

impl<'g> IntoIter<'g> {
    /// Creates a new iterator.
    pub fn new(feature_list: FeatureList<'g>) -> Self {
        Self {
            package_id: feature_list.package.id(),
            iter: feature_list.into_labels().into_iter(),
        }
    }
}

impl<'g> Iterator for IntoIter<'g> {
    type Item = FeatureId<'g>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|label| FeatureId::new(self.package_id, label))
    }
}

/// A borrowed iterator over a `FeatureList`.
pub struct Iter<'g, 'a> {
    package_id: &'g PackageId,
    iter: slice::Iter<'a, FeatureLabel<'g>>,
}

impl<'g, 'a> Iter<'g, 'a> {
    /// Creates a new iterator.
    pub fn new(feature_list: &'a FeatureList<'g>) -> Self {
        Self {
            package_id: feature_list.package.id(),
            iter: feature_list.labels().iter(),
        }
    }
}

impl<'g> Iterator for Iter<'g, '_> {
    type Item = FeatureId<'g>;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter
            .next()
            .map(|&label| FeatureId::new(self.package_id, label))
    }
}

/// A pretty-printer for a list of features.
///
/// Returned by `FeatureList::display_filters`.
#[derive(Clone, Copy)]
pub struct DisplayFeatures<'g, 'a>(&'a [FeatureLabel<'g>]);

impl fmt::Display for DisplayFeatures<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let len = self.0.len();
        for (idx, label) in self.0.iter().enumerate() {
            write!(f, "{label}")?;
            if idx < len - 1 {
                write!(f, ", ")?;
            }
        }
        Ok(())
    }
}

impl fmt::Debug for DisplayFeatures<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Use the Display impl as the debug one because it's easier to read.
        write!(f, "{self}")
    }
}
