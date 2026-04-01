# Note: This Dockerfile must be executed from the `tools/` directory since
# `tools/hermes` relies on `tools/.cargo/config.toml` and `tools/vendor`!
# Usage:
#   cd tools
#   sudo docker build -f hermes/Dockerfile -t hermes-prototype .
FROM ubuntu:24.04 AS base

# Install build dependencies, Rust, and Lean
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential pkg-config libssl-dev && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y && \
    rm -rf /var/lib/apt/lists/*
ENV PATH="/root/.cargo/bin:${PATH}"

# Install elan (Lean toolchain manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# Direct Hermes tests to write ephemeral integration targets here to leverage overlayfs
ENV HERMES_INTEGRATION_TARGET_DIR=/root/.hermes/hermes_target
WORKDIR /workspace

# Copy vendored requirements
COPY .cargo .cargo
COPY vendor vendor

ENV __ZEROCOPY_LOCAL_DEV="1"

# Copy only the hermes crate logic
COPY hermes/Cargo.toml hermes/Cargo.toml
COPY hermes/build.rs hermes/build.rs
COPY hermes/src hermes/src
# Since Cargo.toml explicitly declares [[test]] "integration", this file must exist for Cargo to parse it.
COPY hermes/tests/integration.rs hermes/tests/integration.rs

# Execute purely within the new hermes isolated workspace
WORKDIR /workspace/hermes

# Download and verify the required versions of Charon and Aeneas.
RUN cargo run --bin cargo-hermes setup && \
    rm -rf /workspace/target /workspace/hermes/target /root/.cargo/registry /root/.cargo/git

# Charon strictly requires a specific nightly compiler version to execute.
# FIXME: Extract this version string dynamically from `src/setup.rs` in the future.
RUN rustup toolchain install nightly-2026-02-07 --profile minimal

# To pre-build Mathlib for local development, we run a fast dummy test. We don't
# use this in CI because copying the multiple GB produced in this image is
# slower in CI than just re-building from scratch.
FROM base AS dev
COPY hermes/tests/fixtures/syntax_error tests/fixtures/syntax_error
RUN cargo test --test integration -- syntax_error && \
    rm -rf /workspace/target /workspace/hermes/target /root/.cargo/registry /root/.cargo/git
