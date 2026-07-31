FROM ubuntu:24.04

# Relocate toolchains so that non-root developers can access and write to them
# when mapping UIDs.
ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    ELAN_HOME=/opt/elan \
    PATH="/opt/cargo/bin:/opt/elan/bin:${PATH}"

# Install system dependencies as root.
# We add `graphviz` because it is required by `lake exe graph` to generate
# the dependency graph, and `python3` to run the pruning script.
RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential pkg-config libssl-dev graphviz python3 && \
    rm -rf /var/lib/apt/lists/*

# Create the mapped user and empty directories for toolchains.
# The `-l` flag is passed to `useradd` to avoid creating large sparse files
# for `lastlog` when building with large UIDs. Such sparse files interact
# poorly with Docker's `overlayfs` and can cause massive build delays.
ARG UID
ARG GID
RUN if [ -z "$UID" ]; then echo "UID build arg is required" && exit 1; fi && \
    if [ -z "$GID" ]; then echo "GID build arg is required" && exit 1; fi && \
    sed -i "s/^UID_MAX.*/UID_MAX $UID/" /etc/login.defs && \
    groupadd -g $GID anneal && \
    useradd -l -u $UID -g $GID -m anneal && \
    mkdir /cache /opt/rustup /opt/cargo /opt/elan /workspace /opt/anneal_target /opt/anneal_toolchain && \
    chown anneal:anneal /cache /opt/rustup /opt/cargo /opt/elan /workspace /opt/anneal_target /opt/anneal_toolchain

# Switch to non-root user for the rest of the build.
USER anneal

# Install Rust.
RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path --profile minimal

# Direct Anneal tests to write ephemeral integration targets here to leverage
# overlayfs.
ENV ANNEAL_INTEGRATION_TARGET_DIR=/cache/anneal_target

# In the image, we build dependencies into /opt/anneal_target. This ensures
# they are part of the image and available in CI matrix jobs.
# In local development, docker.sh overrides this to /cache/anneal_target
# via a volume mount, causing dependencies to be rebuilt once in the volume.
# This double-build is intentional to support both environments efficiently.
ENV CARGO_TARGET_DIR=/opt/anneal_target
WORKDIR /workspace/anneal/v1

# Copy the real workspace manifests and lockfile. In particular, do not merge
# doc_gen's dependencies into cargo-anneal: that synthetic package is not what
# Cargo.lock describes, so a locked build would correctly reject it.
COPY --chown=anneal:anneal anneal/v1/Cargo.toml ./Cargo.toml
COPY --chown=anneal:anneal anneal/v1/Cargo.lock ./
COPY --chown=anneal:anneal anneal/v1/tools/doc_gen/Cargo.toml ./tools/doc_gen/Cargo.toml

# Copy source files needed to compile dependency-heavy modules.
COPY --chown=anneal:anneal anneal/v1/src/setup.rs ./src/
COPY --chown=anneal:anneal exocrate/Cargo.toml /workspace/exocrate/Cargo.toml
COPY --chown=anneal:anneal exocrate/src /workspace/exocrate/src
COPY --chown=anneal:anneal anneal/v1/build.rs ./

# Create minimal sources for both workspace members and a dummy test. This
# builds their real locked dependency graph without copying frequently changing
# source files into the dependency-cache layer.
RUN echo 'mod setup; fn main() {}' > src/main.rs && \
    mkdir tests tools/doc_gen/src && \
    echo 'fn main() {}' > tests/integration.rs && \
    echo 'fn main() {}' > tools/doc_gen/src/main.rs

# Build dependencies to cache them in the image.
# Note: We do not use `RUSTFLAGS='-Adead_code'` here (even though the dummy
# `main.rs` has dead code) because doing so would cause Cargo to invalidate
# this cache and rebuild everything when we later run commands *without*
# that flag (which is the default).
RUN cargo build --locked --workspace && \
    cargo build --locked --workspace --tests

# Use a stable shared install root inside test containers. CI installs the
# Nix-built archive here before invoking tests or examples.
ENV ANNEAL_TOOLCHAIN_DIR=/opt/anneal_toolchain

# Ensure the integration target directory exists.
RUN mkdir -p /cache/anneal_target
