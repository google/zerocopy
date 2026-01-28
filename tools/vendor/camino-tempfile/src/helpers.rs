// Copyright (c) The camino-tempfile Contributors
// SPDX-License-Identifier: MIT OR Apache-2.0

use camino::Utf8PathBuf;
use std::{convert::TryFrom, env, io};

pub(crate) fn utf8_env_temp_dir() -> io::Result<Utf8PathBuf> {
    Utf8PathBuf::try_from(env::temp_dir()).map_err(|error| error.into_io_error())
}
