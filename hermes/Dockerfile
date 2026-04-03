FROM ubuntu:24.04 AS base

# Relocate toolchains so non-root developers can access and write to them when mapping UIDs
ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    ELAN_HOME=/opt/elan \
    PATH="/opt/cargo/bin:/opt/elan/bin:${PATH}"

# Install build dependencies, Rust, and Lean
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential pkg-config libssl-dev && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path && \
    rm -rf /var/lib/apt/lists/*

# Install elan (Lean toolchain manager)
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path

# Prepare a globally writable cache directory to hold both the integration test
# outputs and any newly downloaded Cargo crates when a developer binds their
# UID. We make the toolchains globally editable so a host UID can fetch new
# crates.
RUN mkdir -p /cache && chmod 777 /cache && \
    chmod -R a+rwX /opt/rustup /opt/cargo /opt/elan

# Direct Hermes tests to write ephemeral integration targets here to leverage overlayfs
ENV HERMES_INTEGRATION_TARGET_DIR=/cache/hermes_target
WORKDIR /workspace

# Copy vendored requirements
COPY .cargo .cargo
COPY vendor vendor

ENV __ZEROCOPY_LOCAL_DEV="1"

# Copy only the hermes crate logic
COPY Cargo.toml Cargo.toml
COPY build.rs build.rs
COPY src src
# Since Cargo.toml explicitly declares [[test]] "integration", this file must exist for Cargo to parse it.
COPY tests/integration.rs tests/integration.rs

# Download and verify the required versions of Charon and Aeneas.
RUN cargo run --bin cargo-hermes setup && \
    rm -rf /workspace/target /opt/cargo/registry /opt/cargo/git

# Charon strictly requires a specific nightly compiler version to execute.
# FIXME: Extract this version string dynamically from `src/setup.rs` in the future.
RUN rustup toolchain install nightly-2026-02-07 --profile minimal && \
    chmod -R a+rwX /opt/rustup /opt/cargo /opt/elan

# To pre-build Mathlib for local development, we run a fast dummy test. We don't
# use this in CI because copying the multiple GB produced in this image is
# slower in CI than just re-building from scratch.
FROM base AS dev
COPY tests/fixtures/syntax_error tests/fixtures/syntax_error
RUN cargo test --test integration -- syntax_error && \
    chmod -R a+rwX /cache

# Any `/workspace/target` generated here will be shadowed by the host's bind
# mount, so removing it is purely to reduce image size slightly before
# shadowing. Because of this shadowing, there would be no benefit to keeping
# it.
RUN rm -rf /workspace/target
