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

ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    PATH="/usr/local/cargo/bin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    build-essential \
    && rm -rf /var/lib/apt/lists/*

RUN curl -fsSL --retry 3 -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/1.29.3/x86_64-unknown-linux-gnu/rustup-init" && \
    echo "b1c8cb14e30889e7e2999e6b69e62d9e9b9ffc0f4df8180564d306d9680e6c55  /tmp/rustup-init" | sha256sum -c - && \
    chmod 0755 /tmp/rustup-init && \
    /tmp/rustup-init -y --default-toolchain "${PIN_RUST_TOOLCHAINS__STABLE}" --profile minimal --no-modify-path && \
    rm -f /tmp/rustup-init

COPY tools/cargo-zerocopy /tmp/tools/cargo-zerocopy
COPY tools/ui-runner /tmp/tools/ui-runner

RUN cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" build --locked --release \
      --manifest-path /tmp/tools/cargo-zerocopy/Cargo.toml && \
    install -Dm0755 /tmp/tools/cargo-zerocopy/target/release/cargo-zerocopy /out-bin/cargo-zerocopy && \
    cargo "+${PIN_RUST_TOOLCHAINS__STABLE}" build --locked --release \
      --manifest-path /tmp/tools/ui-runner/Cargo.toml && \
    install -Dm0755 /tmp/tools/ui-runner/target/release/ui-runner /out-bin/ui-runner

FROM docker.io/library/ubuntu:24.04@sha256:9a04f13b3f80ef056361e30868593b1cfd2279fe19e4081cb93a90bf56819d6a

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ARG BUILD_RS_TIER
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_ALLOCATOR_API_1_100_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_SIMD_X86_AVX12_1_89_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_AARCH64_SIMD_BE_1_87_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_CORE_ERROR_1_81_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_SLICE_PTR_LEN_1_79_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_DIAGNOSTIC_ON_UNIMPLEMENTED_1_78_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_GENERIC_BOUNDS_IN_CONST_FN_1_61_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_TARGET_HAS_ATOMICS_1_60_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_AARCH64_SIMD_1_59_0
ARG PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_PANIC_IN_CONST_AND_VEC_TRY_RESERVE_1_57_0

ENV CARGO_NET_RETRY=10 \
    RUSTUP_MAX_RETRIES=10 \
    RUSTUP_HOME=/usr/local/rustup \
    CARGO_HOME=/usr/local/cargo \
    CARGO_TERM_COLOR=always \
    CARGO_ZEROCOPY_BIN=/usr/local/bin/cargo-zerocopy \
    ZEROCOPY_UI_RUNNER_BIN=/usr/local/bin/ui-runner \
    PATH="/usr/local/cargo/bin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    gcc-multilib \
    curl \
    jq \
    build-essential \
    python3 \
    && rm -rf /var/lib/apt/lists/*

COPY --from=tool-builder /out-bin/ /usr/local/bin/

RUN curl -fsSL --retry 3 -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/1.29.3/x86_64-unknown-linux-gnu/rustup-init" && \
    echo "b1c8cb14e30889e7e2999e6b69e62d9e9b9ffc0f4df8180564d306d9680e6c55  /tmp/rustup-init" | sha256sum -c - && \
    chmod 0755 /tmp/rustup-init && \
    /tmp/rustup-init -y --default-toolchain none --profile minimal --no-modify-path && \
    rm -f /tmp/rustup-init && \
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
    declare -A seen=() && \
    case "${BUILD_RS_TIER:-}" in \
      modern) \
        TIER_TCS=( \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_ALLOCATOR_API_1_100_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_SIMD_X86_AVX12_1_89_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_AARCH64_SIMD_BE_1_87_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_CORE_ERROR_1_81_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_SLICE_PTR_LEN_1_79_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_DIAGNOSTIC_ON_UNIMPLEMENTED_1_78_0}" \
        ) && \
        for tc in "${TIER_TCS[@]}"; do \
          if [[ -z "${seen[$tc]:-}" ]]; then \
            seen["$tc"]=1; \
            rustup toolchain install "$tc" --profile minimal -c rust-src -c rustfmt -c clippy; \
          fi; \
        done && \
        rustup default "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_ALLOCATOR_API_1_100_0}" && \
        for tc in \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_SIMD_X86_AVX12_1_89_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_SLICE_PTR_LEN_1_79_0}"; do \
          rustup target add --toolchain "$tc" "${BASE_CROSS[@]}" wasm32-unknown-unknown; \
        done && \
        rustup target add --toolchain "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_AARCH64_SIMD_BE_1_87_0}" aarch64-unknown-linux-gnu && \
        for tc in \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_ALLOCATOR_API_1_100_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_CORE_ERROR_1_81_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_DIAGNOSTIC_ON_UNIMPLEMENTED_1_78_0}"; do \
          rustup target add --toolchain "$tc" i686-unknown-linux-gnu; \
        done \
        ;; \
      legacy) \
        TIER_TCS=( \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_GENERIC_BOUNDS_IN_CONST_FN_1_61_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_TARGET_HAS_ATOMICS_1_60_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_AARCH64_SIMD_1_59_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_PANIC_IN_CONST_AND_VEC_TRY_RESERVE_1_57_0}" \
        ) && \
        for tc in "${TIER_TCS[@]}"; do \
          if [[ -z "${seen[$tc]:-}" ]]; then \
            seen["$tc"]=1; \
            rustup toolchain install "$tc" --profile minimal -c rust-src -c rustfmt -c clippy; \
          fi; \
        done && \
        rustup default "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_GENERIC_BOUNDS_IN_CONST_FN_1_61_0}" && \
        for tc in \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_TARGET_HAS_ATOMICS_1_60_0}" \
          "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_PANIC_IN_CONST_AND_VEC_TRY_RESERVE_1_57_0}"; do \
          rustup target add --toolchain "$tc" "${BASE_CROSS[@]}" wasm32-unknown-unknown; \
        done && \
        rustup target add --toolchain "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_AARCH64_SIMD_1_59_0}" aarch64-unknown-linux-gnu && \
        rustup target add --toolchain "${PIN_RUST_TOOLCHAINS__NO_ZEROCOPY_GENERIC_BOUNDS_IN_CONST_FN_1_61_0}" i686-unknown-linux-gnu \
        ;; \
      *) \
        echo "error: unknown BUILD_RS_TIER=${BUILD_RS_TIER:-} (expected modern or legacy)" >&2; \
        exit 1 \
        ;; \
    esac && \
    rm -rf /usr/local/cargo/registry /usr/local/cargo/git \
      /usr/local/rustup/downloads /usr/local/rustup/tmp \
      /usr/local/rustup/toolchains/*/share/doc /usr/local/rustup/toolchains/*/share/man && \
    chmod -R a+rX /usr/local/rustup /usr/local/cargo
