#!/usr/bin/env python3
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Run the shared workflow release-notes generator from its original CLI."""

from pathlib import Path
import runpy


if __name__ == "__main__":
    generator = Path(__file__).resolve().parents[1] / ".github" / "release_notes.py"
    runpy.run_path(str(generator), run_name="__main__")
