# Note: This Dockerfile must be executed from the `tools/` directory since
# `tools/hermes` relies on `tools/.cargo/config.toml` and `tools/vendor`!
# Usage:
#   cd tools
#   sudo docker build -f hermes/Dockerfile -t hermes-prototype .
FROM ubuntu:24.04

# Install build dependencies, Rust, and Lean
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential pkg-config libssl-dev && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

# Install elan (Lean toolchain manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# Direct Hermes tests to write ephemeral integration targets here to leverage overlayfs
ENV HERMES_INTEGRATION_TARGET_DIR=/root/hermes_target
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
RUN cargo run --bin cargo-hermes setup

# Charon strictly requires a specific nightly compiler version to execute.
# FIXME: Extract this version string dynamically from `src/setup.rs` in the future.
RUN rustup toolchain install nightly-2026-02-07 --profile minimal

# To pre-build Mathlib, we only copy the specific `syntax_error` fixture to run a fast dummy test.
COPY hermes/tests/fixtures/syntax_error tests/fixtures/syntax_error
RUN cargo test --test integration -- syntax_error

# We do NOT copy the rest of `hermes` here! The container is strictly a
# pristine, globally-cached execution environment. At runtime, developers
# will bind-mount their live workspace in and run `cargo test` natively.
