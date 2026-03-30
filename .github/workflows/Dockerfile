# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

FROM ubuntu:24.04

# Use `DEBIAN_FRONTEND=noninteractive` to prevent timezone prompts.
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y \
    gcc-multilib \
    llvm \
    curl \
    jq \
    build-essential \
    pkg-config \
    libssl-dev \
    git \
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
    # # FIXME: Kani consumes over 1GB, which imposes a cost every time the image
    # # is downloaded. However, Kani is only used in a single job. We should
    # # create a separate Docker image based on this one which installs Kani last
    # # and is only downloaded by the Kani job.
    # cargo install --locked kani-verifier                    && \
    # cargo kani setup                                        && \
    # Remove large intermediate artifacts to ensure that this step doesn't bloat
    # the Docker image cache.
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
