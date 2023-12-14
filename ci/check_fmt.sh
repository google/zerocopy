#!/bin/bash
set -eo pipefail
cargo fmt --check -p zerocopy
cargo fmt --check -p zerocopy-derive
shopt -s globstar
rustfmt --check tests/**/*.rs
rustfmt --check zerocopy-derive/tests/**/*.rs

