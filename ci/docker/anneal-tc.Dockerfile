# Copyright 2026 The Fuchsia Authors
#
# Licensed under a BSD-style license <LICENSE-BSD>, Apache License, Version 2.0
# <LICENSE-APACHE or https://www.apache.org/licenses/LICENSE-2.0>, or the MIT
# license <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your option.
# This file may not be copied, modified, or distributed except according to
# those terms.

FROM docker.io/library/ubuntu:24.04@sha256:9a04f13b3f80ef056361e30868593b1cfd2279fe19e4081cb93a90bf56819d6a

SHELL ["/bin/bash", "-euo", "pipefail", "-c"]

ENV PATH="/opt/anneal-nix/rust-toolchain/bin:/usr/local/bin:/nix/var/nix/profiles/default/bin:/usr/sbin:/usr/bin:/sbin:/bin" \
    NIX_CONFIG="experimental-features = nix-command flakes" \
    CARGO_TERM_COLOR=always

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
    ca-certificates \
    curl \
    xz-utils \
    zstd \
    jq \
    git \
    ripgrep \
    bubblewrap \
    python3 \
    build-essential \
    pkg-config \
    patchelf \
    zlib1g \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /tmp/dl && \
    curl -fsSL --retry 3 -o /tmp/dl/nix.tar.xz \
      "https://releases.nixos.org/nix/nix-2.26.3/nix-2.26.3-x86_64-linux.tar.xz" && \
    echo "d378a057253fb98f05c3e7c431c1852cca6afae3376f5853a9fcb7ae423a05ad  /tmp/dl/nix.tar.xz" | sha256sum -c - && \
    mkdir -p /tmp/dl/nix-unpack && \
    tar -xJf /tmp/dl/nix.tar.xz -C /tmp/dl/nix-unpack --strip-components=1 && \
    mkdir -p /etc/nix && \
    mkdir -m 0755 -p /nix && \
    printf 'sandbox = false\nexperimental-features = nix-command flakes\nbuild-users-group =\n' > /etc/nix/nix.conf && \
    USER=root HOME=/root /tmp/dl/nix-unpack/install --no-daemon --no-modify-profile && \
    ln -snf "$(readlink -f /root/.nix-profile)" /nix/var/nix/profiles/default && \
    curl -fsSL --retry 3 -o /tmp/dl/nextest.tar.gz "https://get.nexte.st/0.9.152/linux" && \
    echo "d039b43c3e0958441b6ad0a39c8884d018b3d2e8fb9928f209074b1100b5e17a  /tmp/dl/nextest.tar.gz" | sha256sum -c - && \
    tar -xzf /tmp/dl/nextest.tar.gz -C /usr/local/bin cargo-nextest && \
    chmod 0755 /usr/local/bin/cargo-nextest && \
    curl -fsSL --retry 3 -o /usr/local/bin/action-validator \
      "https://github.com/mpalmer/action-validator/releases/download/v0.8.0/action-validator_linux_amd64" && \
    echo "d1d9b787b897c6f8ef9e2f42c2553ce5d0a242aae3bca998d2c67dc69348b128  /usr/local/bin/action-validator" | sha256sum -c - && \
    chmod 0755 /usr/local/bin/action-validator && \
    curl -fsSL --retry 3 -o /usr/local/bin/yq \
      "https://github.com/mikefarah/yq/releases/download/v4.44.1/yq_linux_amd64" && \
    echo "6dc2d0cd4e0caca5aeffd0d784a48263591080e4a0895abe69f3a76eb50d1ba3  /usr/local/bin/yq" | sha256sum -c - && \
    chmod 0755 /usr/local/bin/yq && \
    rm -rf /tmp/dl

COPY anneal/flake.nix /tmp/anneal-seed/anneal/flake.nix
COPY anneal/flake.lock /tmp/anneal-seed/anneal/flake.lock
COPY anneal/Cargo.toml /tmp/anneal-seed/anneal/Cargo.toml
COPY anneal/Cargo.lock /tmp/anneal-seed/anneal/Cargo.lock
COPY anneal/trusted/audit/Cargo.toml /tmp/anneal-seed/anneal/trusted/audit/Cargo.toml
COPY anneal/trusted/cargo-anneal/Cargo.toml /tmp/anneal-seed/anneal/trusted/cargo-anneal/Cargo.toml
COPY anneal/trusted/rustc-capture/Cargo.toml /tmp/anneal-seed/anneal/trusted/rustc-capture/Cargo.toml
COPY anneal/tests/testkit/Cargo.toml /tmp/anneal-seed/anneal/tests/testkit/Cargo.toml
COPY anneal/tests/audit/Cargo.toml /tmp/anneal-seed/anneal/tests/audit/Cargo.toml
COPY anneal/tests/cargo-anneal/Cargo.toml /tmp/anneal-seed/anneal/tests/cargo-anneal/Cargo.toml
COPY anneal/tests/rustc-capture/Cargo.toml /tmp/anneal-seed/anneal/tests/rustc-capture/Cargo.toml
COPY anneal/tests/itree_diff/Cargo.toml /tmp/anneal-seed/anneal/tests/itree_diff/Cargo.toml
COPY anneal/trusted/lean/lean-toolchain /tmp/anneal-seed/anneal/trusted/lean/lean-toolchain
COPY anneal/trusted/lean/foundation-lock.json /tmp/anneal-seed/anneal/trusted/lean/foundation-lock.json
COPY anneal/ci/verify_starnix_e2e.py /tmp/anneal-seed/anneal/ci/verify_starnix_e2e.py
COPY anneal/tests/cargo-anneal/tests/fixtures/starnix/source.json /tmp/anneal-seed/anneal/tests/cargo-anneal/tests/fixtures/starnix/source.json

RUN mkdir -p /opt/nix-cache /opt/anneal-nix/runtime-libs /opt/anneal-cargo-vendor /opt/starnix-ebpf-src \
      /tmp/anneal-seed/anneal/ci \
      /tmp/anneal-seed/anneal/correspondence \
      /tmp/anneal-seed/anneal/theory \
      /tmp/anneal-seed/anneal/trusted/audit/src \
      /tmp/anneal-seed/anneal/trusted/cargo-anneal/examples \
      /tmp/anneal-seed/anneal/trusted/cargo-anneal/src \
      /tmp/anneal-seed/anneal/trusted/correspondence \
      /tmp/anneal-seed/anneal/trusted/rustc-capture/src \
      /tmp/anneal-seed/anneal/vendor/lean-miri \
      /tmp/anneal-seed/anneal/tests/testkit/src \
      /tmp/anneal-seed/anneal/tests/audit/src/bin \
      /tmp/anneal-seed/anneal/tests/cargo-anneal/src/bin \
      /tmp/anneal-seed/anneal/tests/rustc-capture/src/bin \
      /tmp/anneal-seed/anneal/tests/itree_diff/src/bin && \
    touch /tmp/anneal-seed/anneal/ci/prebuild_bundled_oleans.py \
      /tmp/anneal-seed/anneal/ci/render_correspondence_provenance.py \
      /tmp/anneal-seed/anneal/trusted/audit/SpecPreflight.lean \
      /tmp/anneal-seed/anneal/trusted/audit/TrustedBoundary.lean \
      /tmp/anneal-seed/anneal/trusted/audit/library-lock.json \
      /tmp/anneal-seed/anneal/trusted/audit/src/lib.rs \
      /tmp/anneal-seed/anneal/trusted/audit/src/main.rs \
      /tmp/anneal-seed/anneal/trusted/cargo-anneal/examples/regenerate_bundle.rs \
      /tmp/anneal-seed/anneal/trusted/cargo-anneal/src/lib.rs \
      /tmp/anneal-seed/anneal/trusted/cargo-anneal/src/main.rs \
      /tmp/anneal-seed/anneal/trusted/cargo-anneal/src/trusted_bundle.rs \
      /tmp/anneal-seed/anneal/trusted/rustc-capture/src/lib.rs \
      /tmp/anneal-seed/anneal/trusted/rustc-capture/src/main.rs \
      /tmp/anneal-seed/anneal/tests/testkit/src/lib.rs \
      /tmp/anneal-seed/anneal/tests/audit/src/bin/anneal-audit-test-bin.rs \
      /tmp/anneal-seed/anneal/tests/cargo-anneal/src/bin/cargo-anneal-test-bin.rs \
      /tmp/anneal-seed/anneal/tests/rustc-capture/src/bin/anneal-rustc-capture-test-bin.rs \
      /tmp/anneal-seed/anneal/tests/itree_diff/src/lib.rs \
      /tmp/anneal-seed/anneal/tests/itree_diff/src/bin/itree_diff.rs \
      /tmp/anneal-seed/anneal/vendor/lean-miri/UPSTREAM_PIN.json && \
    export XDG_CACHE_HOME=/opt/nix-cache HOME=/root && \
    nix build --no-link --print-out-paths \
      "path:/tmp/anneal-seed/anneal#lean-toolchain" \
      > /tmp/lean-out && \
    ln -snf "$(cat /tmp/lean-out)" /opt/anneal-nix/lean-toolchain && \
    nix build --no-link --print-out-paths \
      "path:/tmp/anneal-seed/anneal#rust-toolchain" \
      > /tmp/rust-out && \
    ln -snf "$(cat /tmp/rust-out)" /opt/anneal-nix/rust-toolchain && \
    nix build --no-link --print-out-paths \
      "path:/tmp/anneal-seed/anneal#release-check-python" \
      > /tmp/py-out && \
    ln -snf "$(cat /tmp/py-out)" /opt/anneal-nix/release-check-python && \
    ZLIB_PATH="$(nix eval --raw --impure --expr '(builtins.getFlake "path:/tmp/anneal-seed/anneal").inputs.nixpkgs.legacyPackages.x86_64-linux.zlib.outPath')" && \
    GCC_LIB_PATH="$(nix eval --raw --impure --expr '(builtins.getFlake "path:/tmp/anneal-seed/anneal").inputs.nixpkgs.legacyPackages.x86_64-linux.stdenv.cc.cc.lib.outPath')" && \
    nix build --no-link "$ZLIB_PATH" "$GCC_LIB_PATH" && \
    cp -L "$ZLIB_PATH/lib/libz.so.1" /opt/anneal-nix/runtime-libs/libz.so.1 && \
    cp -L "$GCC_LIB_PATH/lib/libgcc_s.so.1" /opt/anneal-nix/runtime-libs/libgcc_s.so.1 && \
    printf '%s\n' \
      '#!/usr/bin/env bash' \
      'export LD_LIBRARY_PATH="/opt/anneal-nix/rust-toolchain/lib${LD_LIBRARY_PATH:+:$LD_LIBRARY_PATH}"' \
      'exec /opt/anneal-nix/rust-toolchain/bin/rustc --sysroot /opt/anneal-nix/rust-toolchain -Clinker-features=-lld "$@"' \
      > /opt/anneal-nix/build-rustc && \
    chmod 0755 /opt/anneal-nix/build-rustc && \
    for output in packages devShells; do \
      nix eval --json "path:/tmp/anneal-seed/anneal#$output" \
        --apply 'builtins.mapAttrs (_: builtins.mapAttrs (_: pkg: pkg.drvPath))' >/dev/null; \
    done && \
    RUSTC=/opt/anneal-nix/build-rustc /opt/anneal-nix/rust-toolchain/bin/cargo vendor --locked --versioned-dirs \
      --manifest-path /tmp/anneal-seed/anneal/Cargo.toml \
      /opt/anneal-cargo-vendor >/dev/null && \
    /usr/bin/python3 -I -B /tmp/anneal-seed/anneal/ci/verify_starnix_e2e.py \
      --fetch-only /opt/starnix-ebpf-src && \
    rm -rf /tmp/anneal-seed /tmp/*-out /root/.cargo && \
    chmod -R a+rX /nix /opt/nix-cache /opt/anneal-nix /opt/anneal-cargo-vendor /opt/starnix-ebpf-src
