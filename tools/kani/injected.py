# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Isolate CI-only dependency injection from checked-in/package manifests."""

from contextlib import contextmanager
import json
from pathlib import Path
import shutil
import tempfile


@contextmanager
def injected_crate(repository):
    """Yield a disposable source snapshot with the private Kani macro dependency.

    Copy sources rather than editing the checkout: interrupted verification must
    not leave an unpublished dependency in a manifest used for packaging.
    """
    repository = Path(repository).resolve()
    with tempfile.TemporaryDirectory(prefix="zerocopy-kani-source-") as temporary:
        snapshot = Path(temporary) / "repository"
        shutil.copytree(repository, snapshot, ignore=shutil.ignore_patterns(
            ".git", "target", "__pycache__"))
        crate = snapshot / "zerocopy"
        macro = snapshot / "tools" / "kani-macros"
        with (crate / "Cargo.toml").open("a") as manifest:
            manifest.write("\n[target.'cfg(kani)'.dependencies]\n")
            manifest.write("zerocopy-kani-macros = { path = " +
                           json.dumps(str(macro)) + " }\n")
        yield crate
