# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# `build_docker_env` builds this file as the runtime for typed matrix cells.
# This directory is the complete, isolated Docker context; the producer audit
# rejects any entry other than this file and `.dockerignore`. Keep the complete
# source coordinated with
# `tools/zc/testdata/ci-image.Dockerfile` and
# `tools/zc/src/planned_adapter/image.rs`; the producer audit rejects a
# one-sided change before matrix fan-out.

FROM ubuntu:24.04

# These are the same bounded, download-only retry counts configured in
# `ci.yml`. Defining them before the first networked build step covers rustup
# and Cargo operations while the image is built; the workflow-level values
# cover host operations and are forwarded into containers at runtime.
ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10

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

# Install the three high-traffic toolchains without executing code from the
# checkout. The build previously copied and ran cargo-zerocopy, which made the
# image depend on the entire mutable `tools` tree and allowed a change there to
# replace Cargo before matrix execution. `planned_adapter/image.rs` checks
# these defaults against the validated toolchain inventory, so changing a pin
# in `zerocopy/Cargo.toml` fails CI until this cache seed is updated too.
ARG ZC_MSRV_TOOLCHAIN=1.56.0
ARG ZC_STABLE_TOOLCHAIN=1.93.1
ARG ZC_NIGHTLY_TOOLCHAIN=nightly-2026-01-25
RUN rustup toolchain install "$ZC_MSRV_TOOLCHAIN" \
      -c rust-src -c rustfmt -c clippy && \
    rustup toolchain install "$ZC_STABLE_TOOLCHAIN" \
      -c rust-src -c rustfmt -c clippy && \
    rustup toolchain install "$ZC_NIGHTLY_TOOLCHAIN" \
      -c rust-src -c rustfmt -c clippy -c miri && \
    # Remove large intermediate artifacts to ensure that this step doesn't bloat
    # the Docker image cache.
    rm -rf /root/.cargo/registry /root/.cargo/git /root/.rustup/toolchains/*/share/doc

ENV CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1
WORKDIR /workspace
