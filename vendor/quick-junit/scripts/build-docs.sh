#!/usr/bin/env bash

# Build docs for all crates and direct dependencies. The gawk script turns e.g. "quick-junit v0.1.0"
# into "quick-junit@0.1.0".
cargo tree --depth 1 -e normal --prefix none \
    | gawk '{ gsub(" v", "@", $0); printf("%s\n", $1); }' \
    | xargs printf -- '-p %s\n' \
    | xargs cargo doc --no-deps --lib

# Also drop a _redirects file in the root of the docs directory -- this will be picked up by the
# CI script.
echo "/ /rustdoc/quick_junit/ 301" > target/doc/_redirects
