# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

FROM docker.io/library/ubuntu:24.04@sha256:cd04f18ea6639206fcecf4c148bde909cd08098e1d0569117c2af59242059558

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG PIN_RUST_TOOLCHAINS__STABLE

ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    CARGO_TERM_COLOR=always \
    PATH="/usr/local/cargo/bin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    bubblewrap \
    build-essential \
    ca-certificates \
    curl \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL --retry 3 -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/1.29.3/aarch64-unknown-linux-gnu/rustup-init" && \
    echo "9f608c142e0e38a78957d0661ba1dfaf0b6fb37184cfaa4b9a0aa57af6184282  /tmp/rustup-init" | sha256sum -c - && \
    chmod 0755 /tmp/rustup-init && \
    /tmp/rustup-init -y --default-toolchain "${PIN_RUST_TOOLCHAINS__STABLE}" --profile minimal -c clippy --no-modify-path && \
    rm -f /tmp/rustup-init && \
    rm -rf /usr/local/cargo/registry /usr/local/cargo/git \
      /usr/local/rustup/downloads /usr/local/rustup/tmp \
      /usr/local/rustup/toolchains/*/share/doc /usr/local/rustup/toolchains/*/share/man && \
    chmod -R a+rX /usr/local/rustup /usr/local/cargo
