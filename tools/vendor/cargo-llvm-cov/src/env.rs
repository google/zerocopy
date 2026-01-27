// SPDX-License-Identifier: Apache-2.0 OR MIT

pub(crate) use std::env::*;
use std::ffi::OsString;

use anyhow::Result;
pub(crate) use cargo_config2::{cargo_home_with_cwd, home_dir, rustup_home_with_cwd};

pub(crate) fn var(key: &str) -> Result<Option<String>> {
    match std::env::var(key) {
        Ok(v) if v.is_empty() => Ok(None),
        Ok(v) => Ok(Some(v)),
        Err(VarError::NotPresent) => Ok(None),
        Err(e) => Err(e.into()),
    }
}

pub(crate) fn var_os(key: &str) -> Option<OsString> {
    std::env::var_os(key).filter(|v| !v.is_empty())
}
