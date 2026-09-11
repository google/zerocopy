#syntax=docker/dockerfile:1.5

FROM ubuntu:24.04 as toolchain

ARG channel

ENV DEBIAN_FRONTEND="noninteractive"

# `build-essential` and `file` are needed for backtrace-sys
# `cmake`, `git`, `python` are needed for wasm tools
RUN apt-get update && apt-get install -y \
    build-essential \
    cmake \
    curl \
    file \
    gcc \
    git \
    libssl-dev \
    pkg-config \
 && rm -rf /var/lib/apt/lists/*

RUN useradd -m playground -d /playground
RUN usermod -p '!!' root # Disable all passwords for root

# Attach the security note
COPY --chown=playground attach_notice.sh security_notice.txt /playground/
RUN /playground/attach_notice.sh /playground/security_notice.txt /etc/passwd && \
    /playground/attach_notice.sh /playground/security_notice.txt /etc/shadow && \
    rm -f /playground/attach_notice.sh

USER playground
ENV USER=playground
ENV PATH=/playground/.cargo/bin:/playground/.elan/bin:$PATH
WORKDIR /playground

# Ensure that we are using the latest stable version of rustup and the
# latest version of the current channel. A new manifest will trigger
# these lines to run again, forcing a new download of rustup and
# installation of Rust.
ADD --chown=playground https://static.rust-lang.org/rustup/release-stable.toml /playground/tools/rustup-manifest.toml
ADD --chown=playground https://static.rust-lang.org/dist/channel-rust-${channel}-date.txt /playground/tools/rust-channel-version
RUN curl https://sh.rustup.rs -sSf | sh -s -- \
    -y \
    --profile minimal \
    --default-toolchain "${channel}" \
    --target wasm32-unknown-unknown \
    --component rustfmt \
    --component clippy \
    --component rust-src
RUN if [ "${channel}" = 'nightly' ]; then rustup component add miri; fi

COPY --chown=playground entrypoint.sh /playground/tools/

# Build wasm-tools

FROM toolchain as wasm-tools

RUN cargo install --locked wasm-tools

# Fetch all the crate source files

FROM toolchain as sources

RUN mkdir /playground/src && echo 'fn main() {}' > /playground/src/main.rs
COPY --chown=playground Cargo.toml /playground/Cargo.toml
COPY --chown=playground crate-information.json /playground/crate-information.json
RUN cargo fetch

# Set up cargo-chef for faster builds

FROM toolchain as chef-available

RUN cargo install --locked cargo-chef

WORKDIR /orchestrator

# Prepare the orchestrator's dependencies

FROM chef-available as prepare-orchestrator

COPY --chown=playground asm-cleanup /asm-cleanup
COPY --chown=playground modify-cargo-toml /modify-cargo-toml
COPY --chown=playground orchestrator /orchestrator
RUN cargo chef prepare

# Build the orchestrator

FROM chef-available as build-orchestrator

COPY --chown=playground asm-cleanup /asm-cleanup
COPY --chown=playground modify-cargo-toml /modify-cargo-toml
COPY --chown=playground --from=prepare-orchestrator /orchestrator/recipe.json /orchestrator/recipe.json
RUN cargo chef cook --locked --release

COPY --chown=playground orchestrator /orchestrator
RUN cargo install --locked --path .

# Compiler and pre-compiled crates

FROM sources

ARG channel

RUN cargo build
RUN cargo build --release
RUN cargo clippy
RUN if [ "${channel}" = 'nightly' ]; then cargo miri setup; cargo miri run; fi
COPY --chown=playground cargo-anneal-alpha24-cache-manifest.patch /playground/tools/
RUN <<'EOF'
set -eu
tmp="$(mktemp -d)"
curl -L https://static.crates.io/crates/cargo-anneal/cargo-anneal-0.1.0-alpha.24.crate \
    -o "$tmp/cargo-anneal.crate"
mkdir "$tmp/src"
tar -xzf "$tmp/cargo-anneal.crate" -C "$tmp/src" --strip-components=1
cd "$tmp/src"
git apply /playground/tools/cargo-anneal-alpha24-cache-manifest.patch
cargo install --locked --path .
rm -rf "$tmp"
EOF
RUN cargo anneal setup
RUN <<'EOF'
set -eu
mkdir -p /playground/anneal-workspace/src /playground/anneal-workspace/tmp

cat > /playground/anneal-workspace/Cargo.toml <<'TOML'
[package]
name = "anneal-submission"
version = "0.0.0"
edition = "2021"

[workspace]
TOML

cat > /playground/anneal-workspace/src/main.rs  <<'RS'
/// ```anneal, unsafe(axiom)
/// ```
pub unsafe fn anneal_warmup_identity(x: u32) -> u32 {
    x
}

fn main() {}
RS

cd /playground/anneal-workspace

TMPDIR=/playground/anneal-workspace/tmp \
TEMP=/playground/anneal-workspace/tmp \
TMP=/playground/anneal-workspace/tmp \
CARGO_BUILD_JOBS=2 cargo anneal verify --unsound-allow-is-valid

# Keep reusable Cargo build artifacts, but do not bake Anneal's per-run Lean
# workspace into the image. At runtime, cargo-anneal regenerates that workspace
# and renames its old `.lake` directory into a fresh temporary tree; Docker
# overlayfs can reject that rename when the old tree lives in a read-only image
# layer with "Invalid cross-device link".
find /playground/anneal-workspace/target/anneal \
    -mindepth 1 \
    -maxdepth 1 \
    ! -name cargo_target \
    -exec rm -rf {} +
EOF
COPY --from=build-orchestrator /playground/.cargo/bin/worker /playground/.cargo/bin/worker
COPY --from=wasm-tools /playground/.cargo/bin/wasm-tools /playground/.cargo/bin
COPY --chown=playground cargo-wasm /playground/.cargo/bin
# `cargo-miri-playground` is vestigial and can be removed after a while
COPY --chown=playground cargo-miri-playground /playground/.cargo/bin

ENTRYPOINT ["/playground/tools/entrypoint.sh"]
