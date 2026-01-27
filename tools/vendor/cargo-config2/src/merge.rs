// SPDX-License-Identifier: Apache-2.0 OR MIT

use std::collections::{BTreeMap, btree_map};

use crate::{
    Color, Frequency, When,
    de::{
        self, CredentialProvider, GlobalCredentialProviders, PathAndArgs, RegistriesProtocol,
        VersionControlSoftware,
    },
    error::{Context as _, Result},
    value::Value,
};

// https://github.com/rust-lang/cargo/blob/0.74.0/src/cargo/util/config/mod.rs#L2107-L2115
// TODO:
// - https://github.com/rust-lang/cargo/pull/12515
// - https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/util/context/mod.rs#L2159-L2167
//
// > If `force` is true, primitive (non-container) types will override existing values.
// > If false, the original will be kept and the new value ignored.
// >
// > Container types (tables and arrays) are merged with existing values.
// >
// > Container and non-container types cannot be mixed.
pub(crate) trait Merge {
    /// Merges given config into this config.
    fn merge(&mut self, low: Self, force: bool) -> Result<()>;
}

macro_rules! merge_non_container {
    ($($ty:tt)*) => {
        impl Merge for $($ty)* {
            fn merge(&mut self, low: Self, force: bool) -> Result<()> {
                if force {
                    *self = low;
                }
                Ok(())
            }
        }
        impl Merge for Value<$($ty)*> {
            fn merge(&mut self, low: Self, force: bool) -> Result<()> {
                if force {
                    *self = low;
                }
                Ok(())
            }
        }
    };
}
merge_non_container!(bool);
merge_non_container!(i32);
merge_non_container!(u32);
merge_non_container!(String);
merge_non_container!(Color);
merge_non_container!(VersionControlSoftware);
merge_non_container!(Frequency);
merge_non_container!(When);
merge_non_container!(RegistriesProtocol);
merge_non_container!(CredentialProvider);
merge_non_container!(PathAndArgs); // https://github.com/taiki-e/cargo-config2/issues/26

fn merge_array<T>(this: &mut Vec<T>, mut low: Vec<T>) {
    // https://doc.rust-lang.org/nightly/cargo/reference/config.html#hierarchical-structure
    // > Arrays will be joined together with higher precedence items being placed later in the merged array.
    low.append(this);
    *this = low;
}

impl Merge for GlobalCredentialProviders {
    fn merge(&mut self, low: Self, _force: bool) -> Result<()> {
        merge_array(&mut self.0, low.0);
        Ok(())
    }
}

impl<T: Merge> Merge for Option<T> {
    fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        match (self, low) {
            (_, None) => {}
            (this @ None, low) => *this = low,
            (Some(this), Some(low)) => this.merge(low, force)?,
        }
        Ok(())
    }
}
impl Merge for de::StringOrArray {
    fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        match (self, low) {
            (this @ de::StringOrArray::String(_), low @ de::StringOrArray::String(_)) => {
                if force {
                    *this = low;
                }
            }
            (de::StringOrArray::Array(this), de::StringOrArray::Array(low)) => {
                merge_array(this, low);
            }
            (expected, actual) => {
                bail!("expected {}, but found {}", expected.kind(), actual.kind());
            }
        }
        Ok(())
    }
}
impl Merge for de::StringList {
    fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        match (self.deserialized_repr, low.deserialized_repr) {
            (de::StringListDeserializedRepr::String, de::StringListDeserializedRepr::String) => {
                if force {
                    *self = low;
                }
            }
            (de::StringListDeserializedRepr::Array, de::StringListDeserializedRepr::Array) => {
                merge_array(&mut self.list, low.list);
            }
            (expected, actual) => {
                bail!("expected {}, but found {}", expected.as_str(), actual.as_str());
            }
        }
        Ok(())
    }
}
impl Merge for de::EnvConfigValue {
    fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        match (self, low) {
            (Self::Value(this), Self::Value(low)) => {
                if force {
                    *this = low;
                }
            }
            (
                Self::Table { value: this_value, force: this_force, relative: this_relative },
                Self::Table { value: low_value, force: low_force, relative: low_relative },
            ) => {
                this_value.merge(low_value, force)?;
                this_force.merge(low_force, force)?;
                this_relative.merge(low_relative, force)?;
            }
            (expected, actual) => {
                bail!("expected {}, but found {}", expected.kind(), actual.kind());
            }
        }
        Ok(())
    }
}
impl Merge for de::Flags {
    fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        match (self.deserialized_repr, low.deserialized_repr) {
            (de::StringListDeserializedRepr::String, de::StringListDeserializedRepr::String) => {
                if force {
                    *self = low;
                }
            }
            (de::StringListDeserializedRepr::Array, de::StringListDeserializedRepr::Array) => {
                merge_array(&mut self.flags, low.flags);
            }
            (expected, actual) => {
                bail!("expected {}, but found {}", expected.as_str(), actual.as_str());
            }
        }
        Ok(())
    }
}
impl<V: Merge + Clone + core::fmt::Debug> Merge for BTreeMap<String, V> {
    fn merge(&mut self, low: Self, force: bool) -> Result<()> {
        for (key, value) in low {
            match self.entry(key.clone()) {
                btree_map::Entry::Occupied(mut entry) => {
                    let entry = entry.get_mut();
                    entry.merge(value.clone(), force).with_context(|| {
                        format!(
                            "failed to merge key `{key}` between \
                             {entry:?} and {value:?}", /* TODO: do not use debug output */
                        )
                    })?;
                }
                btree_map::Entry::Vacant(entry) => {
                    entry.insert(value);
                }
            }
        }
        Ok(())
    }
}
