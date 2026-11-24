# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Pin to Ubuntu 24.04 (GCC 13) so CBMC's goto-cc avoids GCC 15 C23 `nullptr_t`
# header incompatibilities in Kani 0.60.x.
FROM docker.io/library/ubuntu:24.04@sha256:9a04f13b3f80ef056361e30868593b1cfd2279fe19e4081cb93a90bf56819d6a

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG PIN_RUST_TOOLCHAINS__STABLE
ARG PIN_KANI_PIN__VERSION
ARG PIN_KANI_PIN__BUNDLE_SHA256

ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    KANI_HOME=/opt/kani \
    CARGO_TERM_COLOR=always \
    PATH="/usr/local/cargo/bin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    build-essential \
    pkg-config \
    libssl-dev \
    jq \
    git \
    python3 \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /tmp/dl /opt/kani && \
    curl -fsSL --retry 3 -o /tmp/dl/rustup-init \
      "https://static.rust-lang.org/rustup/archive/1.29.3/x86_64-unknown-linux-gnu/rustup-init" && \
    echo "b1c8cb14e30889e7e2999e6b69e62d9e9b9ffc0f4df8180564d306d9680e6c55  /tmp/dl/rustup-init" | sha256sum -c - && \
    chmod 0755 /tmp/dl/rustup-init && \
    /tmp/dl/rustup-init -y --default-toolchain "${PIN_RUST_TOOLCHAINS__STABLE}" --profile minimal --no-modify-path && \
    cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" install --locked kani-verifier --version "=${PIN_KANI_PIN__VERSION}" && \
    curl -fsSL --retry 3 -o /tmp/dl/kani-bundle.tar.gz \
      "https://github.com/model-checking/kani/releases/download/kani-${PIN_KANI_PIN__VERSION}/kani-${PIN_KANI_PIN__VERSION}-x86_64-unknown-linux-gnu.tar.gz" && \
    echo "${PIN_KANI_PIN__BUNDLE_SHA256}  /tmp/dl/kani-bundle.tar.gz" | sha256sum -c - && \
    cargo kani setup --use-local-bundle /tmp/dl/kani-bundle.tar.gz && \
    rm -rf /tmp/dl /usr/local/cargo/registry /usr/local/cargo/git \
      /usr/local/rustup/downloads /usr/local/rustup/tmp \
      /usr/local/rustup/toolchains/*/share/doc /usr/local/rustup/toolchains/*/share/man && \
    chmod -R a+rX /usr/local/rustup /usr/local/cargo /opt/kani
