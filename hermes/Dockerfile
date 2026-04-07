FROM ubuntu:24.04 AS base

# Relocate toolchains so non-root developers can access and write to them when
# mapping UIDs.
ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    ELAN_HOME=/opt/elan \
    PATH="/opt/cargo/bin:/opt/elan/bin:${PATH}"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential pkg-config libssl-dev && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path && \
    rm -rf /var/lib/apt/lists/*

# Charon strictly requires a specific nightly compiler version to execute.
# FIXME: Extract this version string dynamically from `src/setup.rs` in the future.
RUN rustup toolchain install --no-self-update nightly-2026-02-07 --profile minimal

# Install elan (Lean toolchain manager).
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path

# Prepare a globally writable cache directory to hold both the integration test
# outputs and any newly downloaded Cargo crates when a developer binds their
# UID. We make the toolchains globally editable so a host UID can fetch new
# crates.
RUN mkdir -p /cache && chmod 777 /cache && \
    chmod -R a+rwX /opt/rustup /opt/cargo /opt/elan

# Direct Hermes tests to write ephemeral integration targets here to leverage
# overlayfs.
ENV HERMES_INTEGRATION_TARGET_DIR=/cache/hermes_target
WORKDIR /workspace

FROM base AS dev

COPY testdata testdata
COPY tools tools

# Download Lean/Elan and pre-build the Mathlib cache and Aeneas standard library.
RUN ./tools/prebuild_lean_libs.sh

RUN chmod -R a+rwX /cache /opt/rustup /opt/cargo /opt/elan
