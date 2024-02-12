#!/bin/bash
set -eo pipefail
cargo fmt --check -p zerocopy
cargo fmt --check -p zerocopy-derive
rustfmt --check $(find tests -iname '*.rs' -type f)
rustfmt --check $(find zerocopy-derive/tests -iname '*.rs' -type f)

