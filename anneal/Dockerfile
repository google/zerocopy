FROM python:3.11-slim AS extractor
WORKDIR /app
COPY Cargo.toml ./
# Remove the [workspace] section so it can be built as a standalone package.
# Also inject tree-sitter dependencies used by doc_gen to cache them too.
RUN sed '1,2d' Cargo.toml > Cargo.toml.no_workspace && \
    sed -i '/^\[dependencies\]$/a tree-sitter = "0.25"\ntree-sitter-lean4 = "0.2"' Cargo.toml.no_workspace

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
WORKDIR /workspace

# Copy the workspace configuration (without workspace section) and lockfile.
COPY --from=extractor --chown=anneal:anneal /app/Cargo.toml.no_workspace ./Cargo.toml
COPY --chown=anneal:anneal Cargo.lock ./

# Copy source files needed for setup.
COPY --chown=anneal:anneal src/setup.rs src/util.rs ./src/
COPY --chown=anneal:anneal build.rs ./
COPY --chown=anneal:anneal tools/prune_mathlib.py ./tools/

# Create a minimal `main.rs` that runs setup, and a dummy test file.
# This allows us to build all dependencies (including dev-dependencies)
# in the image while still being able to run `setup`. It also avoids taking
# a dependency on *most* source files, avoiding unnecessary container rebuilds
# when source files change.
RUN echo 'mod setup; mod util; fn main() -> anyhow::Result<()> { setup::run_setup() }' > src/main.rs && \
    mkdir tests && echo 'fn main() {}' > tests/integration.rs

# Build dependencies to cache them in the image.
# Note: We do not use `RUSTFLAGS='-Adead_code'` here (even though the dummy
# `main.rs` has dead code) because doing so would cause Cargo to invalidate
# this cache and rebuild everything when we later run commands *without*
# that flag (which is the default).
RUN cargo build && \
    cargo build --tests

# Pre-build Lean libraries using the minimal binary.
#
# We also generate the import graph and prune unused Mathlib artifacts here
# to reduce the image size. This must be done after `cargo run` because that
# command fetches and builds the dependencies.
ENV ANNEAL_TOOLCHAIN_DIR=/opt/anneal_toolchain
RUN cargo run && \
    LEAN_DIR=$(find /opt/anneal_toolchain/.anneal/toolchain/ -type d -path "*/backends/lean" | head -n 1) && \
    cd $LEAN_DIR && \
    lake exe graph imports.dot --to Aeneas,Aeneas.Std.Core,Aeneas.Std.WP,Aeneas.Tactic.Solver.ScalarTac,Aeneas.Std.Scalar.Core --include-deps && \
    python3 /workspace/tools/prune_mathlib.py imports.dot .lake/packages/mathlib

# Ensure the integration target directory exists.
RUN mkdir -p /cache/anneal_target
