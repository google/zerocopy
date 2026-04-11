FROM python:3.11-slim AS extractor
WORKDIR /app
COPY Cargo.toml tools/extract_minimal_toml.py ./
RUN python3 extract_minimal_toml.py > Cargo.toml.minimal

FROM ubuntu:24.04

# Relocate toolchains so non-root developers can access and write to them when
# mapping UIDs.
ENV RUSTUP_HOME=/opt/rustup \
    CARGO_HOME=/opt/cargo \
    ELAN_HOME=/opt/elan \
    PATH="/opt/cargo/bin:/opt/elan/bin:${PATH}"

RUN apt-get update && DEBIAN_FRONTEND=noninteractive apt-get install -y git curl build-essential pkg-config libssl-dev && \
    curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y --no-modify-path && \
    rm -rf /var/lib/apt/lists/*

# Charon strictly requires a specific nightly compiler version to execute.
# FIXME: Extract this version string dynamically from `src/setup.rs` in the future.
RUN rustup toolchain install --no-self-update nightly-2026-02-07 --profile minimal

# Install elan (Lean toolchain manager).
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --no-modify-path

# Prepare a globally writable cache directory to hold both the integration test
# outputs and any newly downloaded Cargo crates when a developer binds their
# UID. We make the toolchains globally editable so a host UID can fetch new
# crates.
RUN mkdir -p /cache && chmod 777 /cache && \
    chmod -R a+rwX /opt/rustup /opt/cargo /opt/elan

# Direct Hermes tests to write ephemeral integration targets here to leverage
# overlayfs.
ENV HERMES_INTEGRATION_TARGET_DIR=/cache/hermes_target \
    HERMES_AENEAS_DIR=/cache/hermes_target/hermes_integration_cache
WORKDIR /workspace

# Copy minimal workspace config and minimal source needed for setup
COPY --from=extractor /app/Cargo.toml.minimal ./Cargo.toml
COPY Cargo.lock ./
COPY src/setup.rs src/util.rs ./src/
COPY build.rs ./

# Create a minimal main.rs to build a standalone setup binary
RUN echo 'mod setup; mod util; fn main() -> anyhow::Result<()> { setup::run_setup() }' > src/main.rs

# Build the minimal binary (and cache dependencies)
RUN cargo build

# Pre-build Lean libraries using the minimal binary
ENV HERMES_TOOLCHAIN_DIR=/cache/hermes_toolchain
RUN cargo run setup

RUN chmod -R a+rwX /cache

# Ensure the integration target directory exists and is writable
RUN mkdir -p /cache/hermes_target && chmod 777 /cache/hermes_target
