FROM rust:alpine

RUN apk add musl-dev openssl-dev openssl-libs-static

# Adding -C relocation-model=static due to
# https://github.com/rust-lang/rust/issues/95926

# Adding this to find the statically-built version
ENV OPENSSL_NO_PKG_CONFIG=1 OPENSSL_STATIC=1 OPENSSL_DIR=/usr/

RUN mkdir /output

COPY compiler/base/asm-cleanup /compiler/base/asm-cleanup
COPY compiler/base/orchestrator /compiler/base/orchestrator
COPY compiler/base/modify-cargo-toml /compiler/base/modify-cargo-toml
COPY ui /ui

WORKDIR /compiler/base/orchestrator

RUN \
    cargo rustc --profile test --lib --locked -- --cfg force_docker -C relocation-model=static; \
    test_bin=$(find target/debug/deps/ -name "orchestrator*" -type f -perm -a=x); \
    mv "${test_bin}" /output/unit_tests_orchestrator;

WORKDIR /ui

RUN \
    cargo rustc --tests --locked -- -C relocation-model=static; \
    test_bin=$(find target/debug/deps/ -name "ui*" -type f -perm -a=x); \
    mv "${test_bin}" /output/unit_tests_ui;

# Bake in debug information to debug deadlocks in production
RUN mkdir .cargo
RUN cat <<EOF >.cargo/config.toml
[profile.release]
debug = "full"
split-debuginfo = "off"
EOF

RUN \
    cargo rustc --locked --release -- -C relocation-model=static; \
    mv target/release/ui /output/ui;
