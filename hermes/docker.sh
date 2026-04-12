#!/bin/bash
#
# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# This script executes commands inside a Docker container which has been
# configured to support running integration tests. The container encapsulates
# the toolchain dependencies (Rust, Lean 4, Aeneas, Charon) required by Hermes,
# ensuring consistent execution across setups.
set -eo pipefail

# Determine if the Docker daemon requires root privileges for access. This
# allows the script to operate correctly on systems where the user is not
# a member of the 'docker' group.
if command -v podman >/dev/null 2>&1; then
    DOCKER_CMD=(podman)
else
    DOCKER_CMD=(docker)
    if ! docker info >/dev/null 2>&1; then
        DOCKER_CMD=(sudo docker)
    fi
fi

ARG_UID=$(id -u)
ARG_GID=$(id -g)
if [ "${DOCKER_CMD[0]}" = "podman" ]; then
    # For Podman, use standard small UIDs to avoid exceeding subuid range.
    ARG_UID=1001
    ARG_GID=1001
fi

# Resolve the directory paths required to mount the workspace volume into the
# container. This assumes that the script is located in the root of the
# `hermes` workspace.
DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
IMAGE_NAME="hermes-dev"
VOLUME_NAME="hermes-cache"

BUILD_CACHE=$(mktemp)

# Build the Docker image for the 'dev' stage. If the image is already built
# and cached, the build takes less than a second. We run it in the background
# and capture its output to prevent terminal spam during cached runs. If the
# build takes longer than 5 seconds, we assume a rebuild is occurring and
# stream the output to the terminal so the developer knows why it is pausing.
DOCKER_BUILDKIT=1 "${DOCKER_CMD[@]}" build --progress=plain --build-arg UID=$ARG_UID --build-arg GID=$ARG_GID -t $IMAGE_NAME -f "$DIR/Dockerfile" "$DIR" > "$BUILD_CACHE" 2>&1 &
BUILD_PID=$!

# Wait up to 5 seconds for the build to finish silently.
for i in {1..50}; do
    if ! kill -0 $BUILD_PID 2>/dev/null; then
        break
    fi
    sleep 0.1
done

# If the build is still running, it is likely doing actual work. Stream its
# output to the terminal so the user is not left waiting in silence.
# Wait for the background build process to cleanly exit and capture its status.
# The `||` between `wait $BUILD_PID` and `BUILD_EXIT_CODE=$?` is required
# because, without it, `wait` exits with the same exit code as the PID it's
# waiting for. Combined with `set -e` above, this would cause the script to
# exit `$BUILD_PID` failure, not giving us a chance to print output below.
BUILD_EXIT_CODE=0

if kill -0 $BUILD_PID 2>/dev/null; then
    echo "[docker.sh] Building Docker image; this may take a while..."

    # Start tail in the background to stream output. We avoid `tail --pid` here
    # to ensure cross-platform compatibility with non-GNU systems like macOS.
    tail -n +1 -f "$BUILD_CACHE" &
    TAIL_PID=$!

    wait $BUILD_PID || BUILD_EXIT_CODE=$?

    # Give tail a moment to flush any remaining output before killing it. This
    # mitigates the race condition where tail might be terminated before
    # processing the final lines of the file.
    sleep 0.5
    kill $TAIL_PID 2>/dev/null || true
else
    wait $BUILD_PID || BUILD_EXIT_CODE=$?
fi

if [ $BUILD_EXIT_CODE -ne 0 ]; then
    # If the build failed quickly, the error might not have been streamed.
    # Output the entire file to ensure the error is visible.
    cat "$BUILD_CACHE"
    rm -f "$BUILD_CACHE"
    exit $BUILD_EXIT_CODE
fi

rm -f "$BUILD_CACHE"

# Create the Docker volume used to cache compilation artifacts. A named volume
# is required to persist incremental compilation data between ephemeral
# 'docker run' invocations, decreasing subsequent build times.
if ! "${DOCKER_CMD[@]}" volume inspect $VOLUME_NAME >/dev/null 2>&1; then
    "${DOCKER_CMD[@]}" volume create $VOLUME_NAME >/dev/null
fi

# The '--init' flag ensures that Docker runs an init system as PID 1.
# This allows the container to properly handle signals like SIGINT,
# preventing orphaned toolchain lockfiles from being left behind.
DOCKER_FLAGS=("--rm" "--init")

# Allocate a pseudo-TTY if the script is running in an interactive terminal.
# This preserves colored output from Cargo and other utilities.
if [ -t 0 ] && [ -t 1 ]; then
    DOCKER_FLAGS+=("-t")
fi
DOCKER_FLAGS+=("-i")

# Run the container as the host user's UID and GID. By default, Docker runs
# as root. This flag ensures that any files created within the bind-mounted
# workspace directory are owned by the host user rather than the root user,
# preventing permission errors on the host filesystem.
#
# For Podman, we run as root inside the container. Because Podman is rootless,
# container root maps to the host user, giving us access to the workspace.
# And it allows us to override permissions on files in the image (like /cache).
if [ "${DOCKER_CMD[0]}" = "podman" ]; then
    DOCKER_FLAGS+=("-u" "0")
else
    DOCKER_FLAGS+=("-u" "$ARG_UID:$ARG_GID")
fi

# Disable the PIDs limit to prevent Lean from failing with "failed to create
# thread". Podman has a default PIDs limit (often 2048) that is easily exceeded
# by Lean when it spawns many threads during compilation and verification.
DOCKER_FLAGS+=("--pids-limit=-1")

# Forward all environment variables prefixed with 'HERMES_' to the container.
# This allows developers to interactively override Hermes runtime parameters.
while IFS='=' read -r name value; do
    if [[ $name == HERMES_* ]]; then
        DOCKER_FLAGS+=("-e" "$name")
    fi
done < <(env)

# Forward standard Rust and Hermes tooling environment variables to the
# container if they are defined in the host environment.
#
# FIXME: Maybe prefix `BLESS` as `HERMES_BLESS` so it's automatically forwarded
# by the logic above?
for var in BLESS RUST_LOG RUST_BACKTRACE RUSTFLAGS; do
    if [ "${!var+x}" ]; then
        DOCKER_FLAGS+=("-e" "$var")
    fi
done

# Determine the user's current working directory relative to the repository.
# This path is passed to Docker so that the container executes the requested
# command in the same relative directory as the caller.
REL_PATH=$(realpath --relative-to="$DIR" "$(pwd)" 2>/dev/null || echo ".")
WORKDIR="/workspace/$REL_PATH"

exec "${DOCKER_CMD[@]}" run "${DOCKER_FLAGS[@]}" \
    -v "$DIR:/workspace" \
    -v "$VOLUME_NAME:/cache" \
    -w "$WORKDIR" \
    $IMAGE_NAME "$@"
