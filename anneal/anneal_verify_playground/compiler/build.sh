#!/usr/bin/env bash

set -euv -o pipefail

channels_to_build="${CHANNELS_TO_BUILD-stable beta nightly}"

repository=shepmaster

for channel in $channels_to_build; do
    image_name="rust-${channel}"
    full_name="${repository}/${image_name}"

    docker build \
           -t "${image_name}" \
           -t "${full_name}" \
           --build-arg channel="${channel}" \
           base
done
