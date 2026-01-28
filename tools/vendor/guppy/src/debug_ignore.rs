// Copyright (c) The cargo-guppy Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

//! Contains `DebugIgnore`, a newtype wrapper that causes a field to be ignored while printing
//! out `Debug` output.

use std::{
    fmt,
    ops::{Deref, DerefMut},
};

/// A newtype wrapper that causes this field to be ignored while printing out `Debug` output.
///
/// Similar to `#[derivative(ignore)]`, but avoids an extra dependency.
#[derive(Copy, Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct DebugIgnore<T>(pub T);

impl<T> Deref for DebugIgnore<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl<T> DerefMut for DebugIgnore<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl<T> fmt::Debug for DebugIgnore<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "...")
    }
}
