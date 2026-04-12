FROM python:3.11-slim AS extractor
WORKDIR /app
COPY Cargo.toml tools/extract_minimal_toml.py ./
RUN python3 extract_minimal_toml.py > Cargo.toml.minimal

FROM ubuntu:24.04

# Relocate toolchains so that non-root developers can access and write to them
# when mapping UIDs.
ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    ELAN_HOME=/opt/elan \
    PATH="/opt/cargo/bin:/opt/elan/bin:${PATH}"

# Install system dependencies as root.
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential pkg-config libssl-dev && \
    rm -rf /var/lib/apt/lists/*

# Create the mapped user and empty directories for toolchains.
# The `-l` flag is passed to `useradd` to avoid creating large sparse files
# for `lastlog` when building with large UIDs. Such sparse files interact
# poorly with Docker's `overlayfs` and can cause massive build delays.
ARG UID
ARG GID
RUN if [ -z "$UID" ]; then echo "UID build arg is required" && exit 1; fi && \
    if [ -z "$GID" ]; then echo "GID build arg is required" && exit 1; fi && \
    sed -i "s/^UID_MAX.*/UID_MAX $UID/" /etc/login.defs && \
    groupadd -g $GID hermes && \
    useradd -l -u $UID -g $GID -m hermes && \
    mkdir /cache /opt/rustup /opt/cargo /opt/elan /workspace && \
    chown hermes:hermes /cache /opt/rustup /opt/cargo /opt/elan /workspace

# Switch to non-root user for the rest of the build.
USER hermes

# Install Rust and the specific nightly toolchain required by Charon.
# This version string is hardcoded here and must be kept in sync with
# `Cargo.toml`.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path \
 && rustup toolchain install --no-self-update nightly-2026-02-07 --profile minimal

# Direct Hermes tests to write ephemeral integration targets here to leverage
# overlayfs.
ENV HERMES_INTEGRATION_TARGET_DIR=/cache/hermes_target
WORKDIR /workspace

# Copy the minimal workspace configuration and source files needed for setup.
COPY --from=extractor --chown=hermes:hermes /app/Cargo.toml.minimal ./Cargo.toml
COPY --chown=hermes:hermes Cargo.lock ./
COPY --chown=hermes:hermes src/setup.rs src/util.rs ./src/
COPY --chown=hermes:hermes build.rs ./

# Create a minimal `main.rs` to build a standalone setup binary.
RUN echo 'mod setup; mod util; fn main() -> anyhow::Result<()> { setup::run_setup() }' > src/main.rs

# Build the minimal binary and cache dependencies.
#
# Allow `dead_code` warnings since we have only copied `setup.rs`, and so a lot
# of items are unused. These warnings are harmless.
RUN RUSTFLAGS='-Adead_code' cargo build

# Pre-build Lean libraries using the minimal binary.
ENV HERMES_TOOLCHAIN_DIR=/cache/hermes_toolchain
RUN cargo run setup

# Ensure the integration target directory exists.
RUN mkdir -p /cache/hermes_target
