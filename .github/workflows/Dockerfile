# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

# Build `cargo-nextest` in a disposable stage so the final CI image does not
# carry an unpinned `stable` toolchain or Cargo build artifacts.
FROM ubuntu:24.04 AS nextest-builder

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    PATH="/root/.cargo/bin:${PATH}"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    curl            \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

# Use `default-no-update` (recommended for custom CI builds) to omit the
# self-update networking stack and keep the binary minimal.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --profile minimal && \
    cargo install cargo-nextest --locked --no-default-features --features default-no-update

FROM ubuntu:24.04

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

# These are the same bounded, download-only retry counts configured in
# `ci.yml`. Defining them before the first networked build step covers rustup
# and Cargo operations while the image is built; the workflow-level values
# cover host operations and are forwarded into containers at runtime.
ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    PATH="/root/.cargo/bin:${PATH}"

# Only install packages used by `build_test` and `miri` inside the container.
# `codegen`, `check_readme`, and `check_actions` run on the host runner, so
# `llvm`, `cargo-readme`, `action-validator`, `pkg-config`, and `libssl-dev`
# are omitted. Use `--no-install-recommends` to avoid pulling extra packages.
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    gcc-multilib    \
    curl            \
    jq              \
    build-essential \
    bc              \
    git             \
    && rm -rf /var/lib/apt/lists/*

# Install rustup without an unpinned `stable` toolchain; the pinned `stable`,
# `nightly`, and `msrv` toolchains are installed below from `Cargo.toml`.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --default-toolchain none --profile minimal

COPY --from=nextest-builder /root/.cargo/bin/cargo-nextest /root/.cargo/bin/cargo-nextest

ENV CARGO_ZEROCOPY_AUTO_INSTALL_TOOLCHAIN=1

# Pre-install pinned `stable`, `nightly`, and `msrv` toolchains via bind mounts
# so neither `/tmp/setup` nor `tools/target` enters any image layer.
RUN --mount=type=bind,source=zerocopy/Cargo.toml,target=/mnt/setup/zerocopy/Cargo.toml \
    --mount=type=bind,source=zerocopy/cargo.sh,target=/mnt/setup/zerocopy/cargo.sh     \
    --mount=type=bind,source=tools,target=/mnt/setup/tools                             \
    mkdir -p /tmp/setup/zerocopy && \
    cp /mnt/setup/zerocopy/Cargo.toml /mnt/setup/zerocopy/cargo.sh /tmp/setup/zerocopy/ && \
    cp -a /mnt/setup/tools /tmp/setup/tools && \
    PINNED_STABLE="$(sed -n 's/^[[:space:]]*pinned-stable[[:space:]]*=[[:space:]]*"\([^"]*\)"[[:space:]]*\(#.*\)\{0,1\}$/\1/p' /tmp/setup/zerocopy/Cargo.toml)" && \
    PINNED_STABLE="${PINNED_STABLE%%$'\n'*}" && \
    test -n "$PINNED_STABLE" && \
    rustup toolchain install "$PINNED_STABLE" --profile minimal && \
    rustup default "$PINNED_STABLE" && \
    ( cd /tmp/setup/zerocopy && \
      ./cargo.sh +stable --version  && \
      ./cargo.sh +nightly --version && \
      ./cargo.sh +msrv --version ) && \
    rm -rf /tmp/setup /root/.cargo/registry /root/.cargo/git \
      /root/.rustup/downloads /root/.rustup/tmp \
      /root/.rustup/toolchains/*/share/doc /root/.rustup/toolchains/*/share/man

WORKDIR /workspace
