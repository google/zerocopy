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
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
ENV PATH="/root/.cargo/bin:${PATH}"

RUN cargo install cargo-nextest --locked
RUN cargo install cargo-readme --version 3.2.0
RUN cargo install --locked action-validator --version 0.8.0
RUN cargo install --locked kani-verifier
RUN cargo kani setup

WORKDIR /setup

# FIXME: Don't copy `tools/hermes` so that changes there don't invalidate the
# Docker cache.
COPY Cargo.toml ./
COPY cargo.sh   ./
COPY tools      ./tools

ENV CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1
RUN ./cargo.sh +stable --version && \
    ./cargo.sh +nightly --version && \
    ./cargo.sh +msrv --version

WORKDIR /workspace
