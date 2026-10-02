#!/usr/bin/env bash

set -euv -o pipefail

repository=shepmaster

for image in rust-stable rust-beta rust-nightly; do
    docker pull "${repository}/${image}"
    # The backend expects images without a repository prefix
    docker tag "${repository}/${image}" "${image}"
done
