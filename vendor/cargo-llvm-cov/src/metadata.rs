// SPDX-License-Identifier: Apache-2.0 OR MIT

// Adapted from https://github.com/taiki-e/cargo-hack

use std::{collections::HashMap, ffi::OsStr, path::Path};

use anyhow::{Context as _, Result, format_err};
use camino::{Utf8Path, Utf8PathBuf};
use serde_json::{Map, Value};

type Object = Map<String, Value>;
type ParseResult<T> = Result<T, &'static str>;

/// An opaque unique identifier for referring to the package.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PackageId {
    repr: String,
}

impl From<String> for PackageId {
    fn from(repr: String) -> Self {
        Self { repr }
    }
}

pub(crate) struct Metadata {
    /// List of all packages in the workspace and all feature-enabled dependencies.
    //
    /// This doesn't contain dependencies if cargo-metadata is run with --no-deps.
    pub(crate) packages: HashMap<PackageId, Package>,
    /// List of members of the workspace.
    pub(crate) workspace_members: Vec<PackageId>,
    /// The absolute path to the root of the workspace.
    pub(crate) workspace_root: Utf8PathBuf,
    pub(crate) target_directory: Utf8PathBuf,
    /// This is always `None` if running with a version of Cargo older than 1.91.
    build_directory: Option<Utf8PathBuf>,
}

impl Metadata {
    pub(crate) fn new(manifest_path: &Path, cargo: &OsStr) -> Result<Self> {
        let cmd = cmd!(
            cargo,
            "metadata",
            "--format-version=1",
            "--no-deps",
            "--manifest-path",
            manifest_path
        );
        let json = cmd.read()?;

        let map = serde_json::from_str(&json)
            .with_context(|| format!("failed to parse output from {cmd}"))?;
        Self::from_obj(map).map_err(|s| format_err!("failed to parse `{s}` field from metadata"))
    }

    fn from_obj(mut map: Object) -> ParseResult<Self> {
        let workspace_members: Vec<_> = map
            .remove_array("workspace_members")?
            .into_iter()
            .map(|v| into_string(v).ok_or("workspace_members"))
            .collect::<Result<_, _>>()?;
        Ok(Self {
            packages: map
                .remove_array("packages")?
                .into_iter()
                .map(Package::from_value)
                .collect::<Result<_, _>>()?,
            workspace_members,
            workspace_root: map.remove_string("workspace_root")?,
            target_directory: map.remove_string("target_directory")?,
            // This field was added in Rust 1.91.
            build_directory: if map.contains_key("build_directory") {
                Some(map.remove_string("build_directory")?)
            } else {
                None
            },
        })
    }

    pub(crate) fn build_directory(&self) -> &Utf8Path {
        self.build_directory.as_deref().unwrap_or(&self.target_directory)
    }
}

pub(crate) struct Package {
    /// The name of the package.
    pub(crate) name: String,
    pub(crate) targets: Vec<Target>,
    /// Absolute path to this package's manifest.
    pub(crate) manifest_path: Utf8PathBuf,
}

impl Package {
    fn from_value(mut value: Value) -> ParseResult<(PackageId, Self)> {
        let map = value.as_object_mut().ok_or("packages")?;

        let id = map.remove_string("id")?;
        Ok((id, Self {
            name: map.remove_string("name")?,
            targets: map
                .remove_array("targets")?
                .into_iter()
                .map(Target::from_value)
                .collect::<Result<_, _>>()?,
            manifest_path: map.remove_string("manifest_path")?,
        }))
    }
}

pub(crate) struct Target {
    pub(crate) name: String,
}

impl Target {
    fn from_value(mut value: Value) -> ParseResult<Self> {
        let map = value.as_object_mut().ok_or("targets")?;

        Ok(Self { name: map.remove_string("name")? })
    }
}

// #[allow(clippy::option_option)]
// fn allow_null<T>(value: Value, f: impl FnOnce(Value) -> Option<T>) -> Option<Option<T>> {
//     if value.is_null() { Some(None) } else { f(value).map(Some) }
// }

fn into_string<S: From<String>>(value: Value) -> Option<S> {
    if let Value::String(string) = value { Some(string.into()) } else { None }
}
fn into_array(value: Value) -> Option<Vec<Value>> {
    if let Value::Array(array) = value { Some(array) } else { None }
}
// fn into_object(value: Value) -> Option<Object> {
//     if let Value::Object(object) = value {
//         Some(object)
//     } else {
//         None
//     }
// }

trait ObjectExt {
    fn remove_string<S: From<String>>(&mut self, key: &'static str) -> ParseResult<S>;
    fn remove_array(&mut self, key: &'static str) -> ParseResult<Vec<Value>>;
    // fn remove_object(&mut self, key: &'static str) -> ParseResult<Object>;
    // fn remove_nullable<T>(
    //     &mut self,
    //     key: &'static str,
    //     f: impl FnOnce(Value) -> Option<T>,
    // ) -> ParseResult<Option<T>>;
}

impl ObjectExt for Object {
    fn remove_string<S: From<String>>(&mut self, key: &'static str) -> ParseResult<S> {
        self.remove(key).and_then(into_string).ok_or(key)
    }
    fn remove_array(&mut self, key: &'static str) -> ParseResult<Vec<Value>> {
        self.remove(key).and_then(into_array).ok_or(key)
    }
    // fn remove_object(&mut self, key: &'static str) -> ParseResult<Object> {
    //     self.remove(key).and_then(into_object).ok_or(key)
    // }
    // fn remove_nullable<T>(
    //     &mut self,
    //     key: &'static str,
    //     f: impl FnOnce(Value) -> Option<T>,
    // ) -> ParseResult<Option<T>> {
    //     self.remove(key).and_then(|v| allow_null(v, f)).ok_or(key)
    // }
}
