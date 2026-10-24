#!/usr/bin/env bash

set -eu

IMAGE_NAME=backend-build
OUTPUT_DIR=docker-output

docker build -t "${IMAGE_NAME}" -f ci/Dockerfile .

mkdir -p "${OUTPUT_DIR}"

container_id=$(docker create "${IMAGE_NAME}")
for f in unit_tests_orchestrator unit_tests_ui ui; do
    docker cp "${container_id}:/output/${f}" "${OUTPUT_DIR}"
done
docker rm -f "${container_id}"
