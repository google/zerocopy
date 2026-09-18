#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Apply the locally reviewed patch, after verifying its exact content."""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import subprocess

BRANCH = "refs/heads/fix-transmute-reverse-before"
assert os.environ["GITHUB_REPOSITORY"] == "google/zerocopy"
assert os.environ["GITHUB_REF"] == BRANCH
parts = [Path(f"tools/reverse-before-patch.{i}").read_text().strip() for i in range(5)]
patch = lzma.decompress(base64.b64decode("".join(parts), validate=True))
assert hashlib.sha256(patch).hexdigest() == "954f9ed025e6f636818e09f660e5bf334cdedcaa041de0dc9d330a7423192d94"
expected = {
    "zerocopy/src/impls.rs",
    "zerocopy/src/layout.rs",
    "zerocopy/src/lib.rs",
    "zerocopy/src/pointer/invariant.rs",
    "zerocopy/src/pointer/mod.rs",
    "zerocopy/src/pointer/ptr.rs",
    "zerocopy/src/pointer/transmute.rs",
    "zerocopy/src/pointer/transmute/reverse_tests.rs",
    "zerocopy/src/ref.rs",
    "zerocopy/src/util/macros.rs",
    "zerocopy/src/wrappers.rs",
    "zerocopy/zerocopy-derive/src/derive/project.rs",
}
actual = set()
for line in patch.decode().splitlines():
    if line.startswith("+++ b/"):
        actual.add(line[6:])
assert actual == expected, (actual, expected)
subprocess.run(["git", "apply", "--check", "--unidiff-zero", "-"], input=patch, check=True)
subprocess.run(["git", "apply", "--unidiff-zero", "-"], input=patch, check=True)
subprocess.run(["git", "diff", "--check"], check=True)
Path(os.environ["RUNNER_TEMP"], "reverse-before-paths.txt").write_text("\n".join(sorted(expected)) + "\n")
print("Applied exact reviewed patch to", len(actual), "source files")
