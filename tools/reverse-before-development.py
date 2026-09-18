#!/usr/bin/env python3
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

"""Apply the locally reviewed patches, verifying content before execution."""
import base64
import hashlib
import lzma
import os
from pathlib import Path
import subprocess

assert os.environ["GITHUB_REPOSITORY"] == "google/zerocopy"
assert os.environ["GITHUB_REF"] == "refs/heads/fix-transmute-reverse-before"
expected = {
    "zerocopy/src/impls.rs", "zerocopy/src/layout.rs", "zerocopy/src/lib.rs",
    "zerocopy/src/pointer/invariant.rs", "zerocopy/src/pointer/mod.rs",
    "zerocopy/src/pointer/ptr.rs", "zerocopy/src/pointer/transmute.rs",
    "zerocopy/src/pointer/transmute/reverse_tests.rs", "zerocopy/src/ref.rs",
    "zerocopy/src/util/macros.rs", "zerocopy/src/wrappers.rs",
    "zerocopy/zerocopy-derive/src/derive/project.rs",
}

def apply(data, digest, paths):
    assert hashlib.sha256(data).hexdigest() == digest
    actual = {line[6:] for line in data.decode().splitlines() if line.startswith("+++ b/")}
    assert actual == paths, (actual, paths)
    subprocess.run(["git", "apply", "--check", "--unidiff-zero", "-"], input=data, check=True)
    subprocess.run(["git", "apply", "--unidiff-zero", "-"], input=data, check=True)

parts = [Path(f"tools/reverse-before-patch.{i}").read_text().strip() for i in range(5)]
apply(lzma.decompress(base64.b64decode("".join(parts), validate=True)),
      "954f9ed025e6f636818e09f660e5bf334cdedcaa041de0dc9d330a7423192d94", expected)
fix = "/Td6WFoAAATm1rRGAgAhARYAAAB0L+Wj4BI9BQ9dABboBAwi8+6/wFbOYx+lmlgqI47EQb1coEYZCxs/qNs1NXF41Gq6cSUi71wuLHw6Ca2T6GfkWNv+up82X/cegH8WymJ9yecnZkBZ3oR0+mT2Oa6izc4jpVvDLeXv0Hv/+Z/Rs8IwonkULZweGvgXdyxL62o0OzdMgG9eZSPYai6X0K9Llz5oa4wHX9HoE2uhIx4Uze7sniPAcZY2Q2r3JCPSKphMvkXCmHLZIiUBFoAJasXsPJnFTWwmxMcQlZtuceM0GppEWUgdtdrtMBkUGa/W2yKivxDsav5BDO0TzQJg2cRWZKx8gJ6nW9PeyR378ZiSl0nykhb/8GyO6uTwMlY4R9obN5AsQvnKvkcbmSJqHkx54pq5qsjOYVQjG/ooGyr7SuYPq8hVVOJ2SgYK6GOt7ofc/nUvMXd/kX48hU1kkI8FGxkCVZHGkqDQv5IRIdk5dGM4GTOAx7qZxUwtQ1LoZvy6ci6uR+KINHDJ3ETbIdAMVArQq8kVkzy/1G0LM0epV/mbNBVf3wu09ZXjlueMX1N1sFuW+M5Elj+X25dpGUQrIQ9KCNvVyIpfMHgX8zgVbE4CEq/oqISZ5gLkpdETqfLdeEBMVkovBZ/pJ+mU7f0JudXc/YcHeI1mDTI1/0vDu6aAs4B8TKGOieICpJ/OfRQZV08qk9nxLZOHElIHViKExAqh7tBl0Gsrsxa3KtGWMvz9FyhLIGPhHc0Z/RJCeMDTeGQsQkQ1TVsv+R2/Bh56UFoY9cGqRqspAUfzVppZHvMZHEr9iZDUSZdapWQAtF6ZNsCmD+iLS2t6mplPY5E3k3hZ3XnTuiKq4bF4MmTcihFUCzmMYSFZUtllshYhsgv3M/hmdbbHSjgaA5BGp5TPA7zM02HAWO9PHDP9K9psfMHVcPCB2PnxIgGeo4qlnTbHuKoJdLliQE2mVjLDU0zNRyT4xPxHlxaHWw7Ew/tvLf11Ofw+Gw37DKQnno47+WnuXpRxfmZ52NG/kCzqE8ieETsCn0i9S9vqag02S34m5EGQweQ5IWuef3+RnAqFXxz9tuggyq/EAZ0efrsuZnUtfUULkrONJTHIpZD3H8KTO4Ln2mcjN55fL8bZtj2oPHSLI1nF+mklveK3FhInsZp76Y7FNaAWhJuLK0Q2ZTRI9Me0ksdDxIh6jMkaF5aFHxxfzrnU3GvayMF6uCo/spcEzp8YVxPfBkRmhv1CC2c7xt/uz1uODIbJXABZYwCIyXuAL6oALyIgY0el+kH4AJCadVjq1FLbBpL8foVy6JqdkMXRgWBIDKDFhfT14HUQGgPZjo1mBkDdjyCIskvW8kYT8DOSmj3s8xXhSJmiyBeHDTCVCFob7ZAMFcQwQ6LAFtgYDe4/tIw4h2m6Ax7Ezpls89RCHWOemN3dJE4IkguqPdLXAvM/aANZklh3yUMvBmyAjVdsJaoqbq6MUCXzlCMaDrB3pq4UgSvZWw9cVYyx/9IpgVlgtzGYGHRBk/kwnbBSQFcDJ0EYw4CyrrS0sabYeY0IB0V6JRnrbrvI9LIIAFgB8IayjQcYIXikm3DmYT7UjgFw/m4VePYVoW8kT+O6JpqaKGS1n41MzskOvy9W3PlqEU0+QHf1c2C5tfPsm121b0x4Hh4Ur/lU2zNO20RQ2cKeYUvZAqW4c1Q1OcW1x3pbec8wnSe5pMXo0WgABSi4mE0gX2wcn9K6UZer9kjrcigA50GwshMNCxvDAAD/aF6/Fv0miwABqwq+JAAAxPrXOLHEZ/sCAAAAAARZWg=="
apply(lzma.decompress(base64.b64decode(fix, validate=True)),
      "9d63e07cc2a988474f9f088c99e92d4b9b239b27899498d7aaf948789b35046b",
      {"zerocopy/src/wrappers.rs", "zerocopy/src/pointer/transmute.rs", "zerocopy/src/pointer/ptr.rs"})
subprocess.run(["git", "diff", "--check"], check=True)
Path(os.environ["RUNNER_TEMP"], "reverse-before-paths.txt").write_text("\n".join(sorted(expected)) + "\n")
print("Applied exact reviewed patches to", len(expected), "source files")
