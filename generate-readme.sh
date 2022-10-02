#!/bin/bash
#
# Copyright 2018 The Fuchsia Authors. All rights reserved.
# Use of this source code is governed by a BSD-style license that can be
# found in the LICENSE file.

set -e

COPYRIGHT_HEADER=$(mktemp)
BODY=$(mktemp)
DISCLAIMER_FOOTER=$(mktemp)

cat > $COPYRIGHT_HEADER <<EOF
<!-- Copyright 2022 The Fuchsia Authors. All rights reserved.
Use of this source code is governed by a BSD-style license that can be
found in the LICENSE file. -->

EOF

# This uses the `cargo readme` tool, which you can install via `cargo install
# cargo-readme --version 3.2.0`.
#
# The `sed` command is used to strip code links like:
#
#   /// Here is a link to [`Vec`].
#
# These links don't work in a Markdown file, and so we remove the `[` and `]`
# characters to convert them to non-link code snippets.
cargo readme | sed 's/\[\(`[^`]*`\)]/\1/g' > $BODY

cat > $DISCLAIMER_FOOTER <<EOF

## Dislcaimer

Disclaimer: Zerocopy is not an officially supported Google product.
EOF

cat $COPYRIGHT_HEADER $BODY $DISCLAIMER_FOOTER