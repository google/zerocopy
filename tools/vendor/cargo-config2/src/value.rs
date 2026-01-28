// SPDX-License-Identifier: Apache-2.0 OR MIT

// Based on https://github.com/rust-lang/cargo/blob/0.80.0/src/cargo/util/context/value.rs.

use core::{fmt, mem, str::FromStr};
use std::{
    borrow::Cow,
    collections::BTreeMap,
    path::{Path, PathBuf},
};

use serde_derive::{Deserialize, Serialize};

use crate::error::Result;

#[allow(clippy::exhaustive_structs)]
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(transparent)]
pub struct Value<T> {
    /// The inner value that was deserialized.
    pub val: T,
    /// The location where `val` was defined in configuration (e.g. file it was
    /// defined in, env var etc).
    #[serde(skip)]
    pub definition: Option<Definition>,
}

impl Value<String> {
    pub(crate) fn parse<T: FromStr>(self) -> Result<Value<T>, T::Err> {
        Ok(Value { val: self.val.parse()?, definition: self.definition })
    }
    // https://doc.rust-lang.org/nightly/cargo/reference/config.html#config-relative-paths
    pub(crate) fn resolve_as_program_path(&self, current_dir: &Path) -> Cow<'_, Path> {
        match &self.definition {
            Some(def)
                if !Path::new(&self.val).is_absolute()
                    && (self.val.contains('/') || self.val.contains('\\')) =>
            {
                def.root(current_dir).join(&self.val).into()
            }
            _ => Path::new(&self.val).into(),
        }
    }
    pub(crate) fn resolve_as_path(&self, current_dir: &Path) -> Cow<'_, Path> {
        match &self.definition {
            Some(def) if !Path::new(&self.val).is_absolute() => {
                def.root(current_dir).join(&self.val).into()
            }
            _ => Path::new(&self.val).into(),
        }
    }
}

/// Location where a config value is defined.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub enum Definition {
    /// Defined in a `.cargo/config`, includes the path to the file.
    Path(PathBuf),
    /// Defined in an environment variable, includes the environment key.
    Environment(Cow<'static, str>),
    /// Passed in on the command line.
    /// A path is attached when the config value is a path to a config file.
    Cli(Option<PathBuf>),
}

impl Definition {
    /// Root directory where this is defined.
    ///
    /// If from a file, it is the directory above `.cargo/config`.
    /// CLI and env are the current working directory.
    pub(crate) fn root<'a>(&'a self, current_dir: &'a Path) -> &'a Path {
        match self {
            Definition::Path(p) | Definition::Cli(Some(p)) => p.parent().unwrap().parent().unwrap(),
            Definition::Environment(_) | Definition::Cli(None) => current_dir,
        }
    }
    pub(crate) fn root_opt<'a>(&'a self, current_dir: Option<&'a Path>) -> Option<&'a Path> {
        match self {
            Definition::Path(p) | Definition::Cli(Some(p)) => {
                Some(p.parent().unwrap().parent().unwrap())
            }
            Definition::Environment(_) | Definition::Cli(None) => current_dir,
        }
    }

    // /// Returns `true` if self is a higher priority to other.
    // ///
    // /// CLI is preferred over environment, which is preferred over files.
    // pub(crate) fn is_higher_priority(&self, other: &Definition) -> bool {
    //     matches!(
    //         (self, other),
    //         (Definition::Cli(_), Definition::Environment(_) | Definition::Path(_))
    //             | (Definition::Environment(_), Definition::Path(_))
    //     )
    // }
}

impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Definition::Path(p) | Definition::Cli(Some(p)) => p.display().fmt(f),
            Definition::Environment(key) => write!(f, "environment variable `{key}`"),
            Definition::Cli(None) => f.write_str("--config cli option"),
        }
    }
}

impl PartialEq for Definition {
    fn eq(&self, other: &Definition) -> bool {
        // configuration values are equivalent no matter where they're defined,
        // but they need to be defined in the same location. For example if
        // they're defined in the environment that's different than being
        // defined in a file due to path interpretations.
        mem::discriminant(self) == mem::discriminant(other)
    }
}

pub(crate) trait SetPath {
    fn set_path(&mut self, path: &Path);
}
impl<T: SetPath> SetPath for Option<T> {
    fn set_path(&mut self, path: &Path) {
        if let Some(v) = self {
            v.set_path(path);
        }
    }
}
impl<T: SetPath> SetPath for Vec<T> {
    fn set_path(&mut self, path: &Path) {
        for v in self {
            v.set_path(path);
        }
    }
}
impl<T: SetPath> SetPath for BTreeMap<String, T> {
    fn set_path(&mut self, path: &Path) {
        for v in self.values_mut() {
            v.set_path(path);
        }
    }
}
impl<T> SetPath for Value<T> {
    fn set_path(&mut self, path: &Path) {
        self.definition = Some(Definition::Path(path.to_owned()));
    }
}
