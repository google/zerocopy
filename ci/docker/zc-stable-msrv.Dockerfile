# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

FROM docker.io/library/ubuntu:24.04@sha256:9a04f13b3f80ef056361e30868593b1cfd2279fe19e4081cb93a90bf56819d6a AS tool-builder

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG PIN_RUST_TOOLCHAINS__STABLE
ARG PIN_SEMVER_BASELINE__VERSION
ARG PIN_SEMVER_BASELINE__CRATE_SHA256
ARG PIN_SEMVER_BASELINE__TOOL_VERSION
ARG PIN_SEMVER_BASELINE__TOOL_SHA256

ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH="/usr/local/cargo/bin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    xz-utils \
    build-essential \
    pkg-config \
    libssl-dev \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL --retry 3 -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/1.29.3/x86_64-unknown-linux-gnu/rustup-init" && \
    echo "b1c8cb14e30889e7e2999e6b69e62d9e9b9ffc0f4df8180564d306d9680e6c55  /tmp/rustup-init" | sha256sum -c - && \
    chmod 0755 /tmp/rustup-init && \
    /tmp/rustup-init -y --default-toolchain "${PIN_RUST_TOOLCHAINS__STABLE}" --profile minimal --no-modify-path && \
    rm -f /tmp/rustup-init

COPY tools/cargo-zerocopy /tmp/tools/cargo-zerocopy
COPY tools/generate-readme /tmp/tools/generate-readme
COPY tools/ui-runner /tmp/tools/ui-runner

RUN cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" build --locked --release \
      --manifest-path /tmp/tools/cargo-zerocopy/Cargo.toml && \
    install -Dm0755 /tmp/tools/cargo-zerocopy/target/release/cargo-zerocopy /out-bin/cargo-zerocopy && \
    cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" build --locked --release \
      --manifest-path /tmp/tools/generate-readme/Cargo.toml && \
    install -Dm0755 /tmp/tools/generate-readme/target/release/generate-readme /out-bin/generate-readme && \
    cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" build --locked --release \
      --manifest-path /tmp/tools/ui-runner/Cargo.toml && \
    install -Dm0755 /tmp/tools/ui-runner/target/release/ui-runner /out-bin/ui-runner && \
    cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" install --locked --version '=3.2.0' cargo-readme && \
    install -Dm0755 /usr/local/cargo/bin/cargo-readme /out-bin/cargo-readme

RUN mkdir -p /tmp/dl && \
    curl -fsSL --retry 3 -o /tmp/dl/nextest.tar.gz "https://get.nexte.st/0.9.152/linux" && \
    echo "d039b43c3e0958441b6ad0a39c8884d018b3d2e8fb9928f209074b1100b5e17a  /tmp/dl/nextest.tar.gz" | sha256sum -c - && \
    tar -xzf /tmp/dl/nextest.tar.gz -C /out-bin cargo-nextest && \
    chmod 0755 /out-bin/cargo-nextest && \
    curl -fsSL --retry 3 -o /tmp/dl/csc.tar.gz \
      "https://github.com/obi1kenobi/cargo-semver-checks/releases/download/v${PIN_SEMVER_BASELINE__TOOL_VERSION}/cargo-semver-checks-x86_64-unknown-linux-gnu.tar.gz" && \
    echo "${PIN_SEMVER_BASELINE__TOOL_SHA256}  /tmp/dl/csc.tar.gz" | sha256sum -c - && \
    tar -xzf /tmp/dl/csc.tar.gz -C /out-bin cargo-semver-checks && \
    chmod 0755 /out-bin/cargo-semver-checks && \
    curl -fsSL --retry 3 -o /out-bin/action-validator \
      "https://github.com/mpalmer/action-validator/releases/download/v0.8.0/action-validator_linux_amd64" && \
    echo "d1d9b787b897c6f8ef9e2f42c2553ce5d0a242aae3bca998d2c67dc69348b128  /out-bin/action-validator" | sha256sum -c - && \
    chmod 0755 /out-bin/action-validator && \
    curl -fsSL --retry 3 -o /tmp/dl/zizmor.tar.gz \
      "https://github.com/zizmorcore/zizmor/releases/download/v1.23.1/zizmor-x86_64-unknown-linux-gnu.tar.gz" && \
    echo "67a8df0a14352dd81882e14876653d097b99b0f4f6b6fe798edc0320cff27aff  /tmp/dl/zizmor.tar.gz" | sha256sum -c - && \
    tar -xzf /tmp/dl/zizmor.tar.gz -C /out-bin ./zizmor && \
    chmod 0755 /out-bin/zizmor && \
    curl -fsSL --retry 3 -o /out-bin/yq \
      "https://github.com/mikefarah/yq/releases/download/v4.44.1/yq_linux_amd64" && \
    echo "6dc2d0cd4e0caca5aeffd0d784a48263591080e4a0895abe69f3a76eb50d1ba3  /out-bin/yq" | sha256sum -c - && \
    chmod 0755 /out-bin/yq && \
    curl -fsSL --retry 3 -o /tmp/dl/shellcheck.tar.xz \
      "https://github.com/koalaman/shellcheck/releases/download/v0.10.0/shellcheck-v0.10.0.linux.x86_64.tar.xz" && \
    echo "6c881ab0698e4e6ea235245f22832860544f17ba386442fe7e9d629f8cbedf87  /tmp/dl/shellcheck.tar.xz" | sha256sum -c - && \
    tar -xJf /tmp/dl/shellcheck.tar.xz --strip-components=1 -C /out-bin shellcheck-v0.10.0/shellcheck && \
    chmod 0755 /out-bin/shellcheck && \
    rm -rf /tmp/dl

RUN SEMVER_TARGETS=( \
      i686-unknown-linux-gnu \
      x86_64-unknown-linux-gnu \
      x86_64-pc-windows-msvc \
      arm-unknown-linux-gnueabi \
      aarch64-unknown-linux-gnu \
      powerpc-unknown-linux-gnu \
      powerpc64-unknown-linux-gnu \
      riscv64gc-unknown-linux-gnu \
      s390x-unknown-linux-gnu \
    ) && \
    rustup target add --toolchain "${PIN_RUST_TOOLCHAINS__STABLE}" "${SEMVER_TARGETS[@]}" && \
    mkdir -p /tmp/semver-base /opt/semver-baseline/rustdoc && \
    curl -fsSL --retry 3 -o /tmp/zerocopy-base.crate \
      "https://static.crates.io/crates/zerocopy/zerocopy-${PIN_SEMVER_BASELINE__VERSION}.crate" && \
    echo "${PIN_SEMVER_BASELINE__CRATE_SHA256}  /tmp/zerocopy-base.crate" | sha256sum -c - && \
    tar -xzf /tmp/zerocopy-base.crate --strip-components=1 -C /tmp/semver-base && \
    for target in "${SEMVER_TARGETS[@]}"; do \
      RUSTC_BOOTSTRAP=1 \
      RUSTDOCFLAGS="-Z unstable-options --output-format json --cap-lints allow" \
      CARGO_TARGET_DIR=/tmp/semver-target \
      cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" doc \
        --manifest-path /tmp/semver-base/Cargo.toml \
        --no-deps \
        --no-default-features \
        --features __internal_use_only_features_that_work_on_stable \
        --target "$target" && \
      install -Dm0644 "/tmp/semver-target/${target}/doc/zerocopy.json" \
        "/opt/semver-baseline/rustdoc/${target}.json"; \
    done && \
    rm -rf /tmp/semver-base /tmp/semver-target /tmp/zerocopy-base.crate

FROM docker.io/library/ubuntu:24.04@sha256:9a04f13b3f80ef056361e30868593b1cfd2279fe19e4081cb93a90bf56819d6a

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG PIN_RUST_TOOLCHAINS__MSRV
ARG PIN_RUST_TOOLCHAINS__STABLE

ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    CARGO_TERM_COLOR=always \
    CARGO_ZEROCOPY_BIN=/usr/local/bin/cargo-zerocopy \
    ZEROCOPY_UI_RUNNER_BIN=/usr/local/bin/ui-runner \
    GENERATE_README_BIN=/usr/local/bin/generate-readme \
    PATH="/usr/local/cargo/bin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    gcc-multilib \
    curl \
    jq \
    build-essential \
    bc \
    git \
    ripgrep \
    python3 \
    && rm -rf /var/lib/apt/lists/*

COPY --from=tool-builder /out-bin/ /usr/local/bin/
COPY --from=tool-builder /opt/semver-baseline/rustdoc /opt/semver-baseline/rustdoc

RUN curl -fsSL --retry 3 -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/1.29.3/x86_64-unknown-linux-gnu/rustup-init" && \
    echo "b1c8cb14e30889e7e2999e6b69e62d9e9b9ffc0f4df8180564d306d9680e6c55  /tmp/rustup-init" | sha256sum -c - && \
    chmod 0755 /tmp/rustup-init && \
    /tmp/rustup-init -y --default-toolchain none --profile minimal --no-modify-path && \
    rm -f /tmp/rustup-init && \
    declare -A seen=() && \
    for tc in \
      "${PIN_RUST_TOOLCHAINS__STABLE}" \
      "${PIN_RUST_TOOLCHAINS__MSRV}"; do \
      if [[ -z "${seen[$tc]:-}" ]]; then \
        seen["$tc"]=1; \
        rustup toolchain install "$tc" --profile minimal -c rust-src -c rustfmt -c clippy; \
      fi; \
    done && \
    rustup default "${PIN_RUST_TOOLCHAINS__STABLE}" && \
    BASE_CROSS=( \
      i686-unknown-linux-gnu \
      x86_64-pc-windows-msvc \
      arm-unknown-linux-gnueabi \
      aarch64-unknown-linux-gnu \
      powerpc-unknown-linux-gnu \
      powerpc64-unknown-linux-gnu \
      riscv64gc-unknown-linux-gnu \
      s390x-unknown-linux-gnu \
      thumbv6m-none-eabi \
    ) && \
    rustup target add --toolchain "${PIN_RUST_TOOLCHAINS__STABLE}" "${BASE_CROSS[@]}" && \
    rustup target add --toolchain "${PIN_RUST_TOOLCHAINS__MSRV}" "${BASE_CROSS[@]}" wasm32-unknown-unknown && \
    rm -rf /usr/local/cargo/registry /usr/local/cargo/git \
      /usr/local/rustup/downloads /usr/local/rustup/tmp \
      /usr/local/rustup/toolchains/*/share/doc /usr/local/rustup/toolchains/*/share/man && \
    chmod -R a+rX /usr/local/rustup /usr/local/cargo /opt/semver-baseline
