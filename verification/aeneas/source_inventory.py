# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Enumerate the complete source tree shared by discovery and input admission.

A directory name or Git ignore rule cannot exempt a Rust specification from CI.
This inventory therefore has no cache exclusions. Reject symbolic links rather
than silently skipping linked directories or depending on files outside the
checkout. An unreadable directory must also fail, not look like an empty one.
"""

import os
from pathlib import Path


def crate_files(root):
    """Return all source files, including inactive and currently unused modules."""
    source = root / 'zerocopy/src'
    for path in (root / 'zerocopy', source):
        if path.is_symlink():
            raise ValueError(f'Symbolic links in the mandatory source tree are unsupported: {path}')
    if not source.is_dir():
        raise ValueError(f'Missing mandatory source tree: {source}')

    def unreadable(error):
        raise ValueError(f'Cannot inspect the mandatory source tree: {error}') from error

    paths = []
    for directory, dirs, files in os.walk(source, onerror=unreadable):
        for name in [*dirs, *files]:
            path = Path(directory) / name
            if path.is_symlink():
                raise ValueError(f'Symbolic links in the mandatory source tree are unsupported: {path}')
        paths.extend(Path(directory) / name for name in files)
    return sorted(paths)
