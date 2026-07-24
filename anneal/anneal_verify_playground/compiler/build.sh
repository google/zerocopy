#!/usr/bin/env bash

set -euv -o pipefail

channels_to_build="${CHANNELS_TO_BUILD-stable beta nightly}"

repository=shepmaster

for channel in $channels_to_build; do
    image_name="rust-${channel}"
    full_name="${repository}/${image_name}"

    build_start_ms=$(date +%s%3N)
    echo "[anneal-build-timing] image=${image_name} event=start epoch_ms=${build_start_ms}"

    docker build \
           -t "${image_name}" \
           -t "${full_name}" \
           --build-arg channel="${channel}" \
           base

    build_end_ms=$(date +%s%3N)
    echo "[anneal-build-timing] image=${image_name} event=finish epoch_ms=${build_end_ms} elapsed_ms=$((build_end_ms - build_start_ms))"
done
