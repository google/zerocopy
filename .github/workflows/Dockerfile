# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

FROM ubuntu:24.04 AS base

# Use `DEBIAN_FRONTEND=noninteractive` to prevent timezone prompts.
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    gcc-multilib    \
    llvm            \
    curl            \
    jq              \
    build-essential \
    pkg-config      \
    libssl-dev      \
    bc              \
    git             \
    # Remove large intermediate artifacts to ensure that this step doesn't bloat
    # the Docker image cache.
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal && \
    # Remove large intermediate artifacts to ensure that this step doesn't bloat
    # the Docker image cache.
    rm -rf /root/.cargo/registry /root/.cargo/git

ENV PATH="/root/.cargo/bin:${PATH}"

RUN cargo install cargo-nextest --locked                    && \
    cargo install cargo-readme --version 3.2.0              && \
    cargo install --locked action-validator --version 0.8.0 && \
    rm -rf /root/.cargo/registry /root/.cargo/git

WORKDIR /setup

# FIXME: Don't copy `tools/hermes` so that changes there don't invalidate the
# Docker cache.
COPY Cargo.toml ./
COPY cargo.sh   ./
COPY tools      ./tools

ENV CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1
RUN ./cargo.sh +stable --version  && \
    ./cargo.sh +nightly --version && \
    ./cargo.sh +msrv --version    && \
    # Remove large intermediate artifacts to ensure that this step doesn't bloat
    # the Docker image cache.
    rm -rf /root/.cargo/registry /root/.cargo/git /root/.rustup/toolchains/*/share/doc

WORKDIR /workspace

FROM base AS hermes

WORKDIR /setup

# Install elan (Lean toolchain manager).
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

RUN cd tools/hermes && \
    CHARON_TOOLCHAIN="$(cargo metadata --no-deps --format-version 1 | jq -r '.packages[] | select(.name == "cargo-hermes") | .metadata.build_rs.charon_rust_toolchain')" && \
    rustup toolchain install "$CHARON_TOOLCHAIN" && \
    # Remove large intermediate artifacts to ensure that this step doesn't bloat
    # the Docker image cache.
    rm -rf /root/.cargo/registry /root/.cargo/git /root/.rustup/toolchains/*/share/doc

# Setup Hermes (Installs Charon and Aeneas binaries).
RUN cd tools/hermes && cargo run --bin cargo-hermes -- setup

# Pre-build Lean dependencies (Mathlib, etc.) and Charon caches by running
# Hermes integration tests.
RUN cd tools/hermes && (cargo test --test integration || true) && \
    # Remove large intermediate artifacts to ensure that this step doesn't bloat
    # the Docker image cache.
    rm -rf /root/.cargo/registry /root/.cargo/git /root/.rustup/toolchains/*/share/doc

WORKDIR /workspace
