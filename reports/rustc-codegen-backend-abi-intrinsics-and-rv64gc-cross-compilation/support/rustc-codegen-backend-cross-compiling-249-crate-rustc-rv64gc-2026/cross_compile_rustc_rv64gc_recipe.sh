#!/usr/bin/env bash
# Self-contained cross-compilation recipe for building all 249 target crates of
# the `rust-lang/rust` (`compiler/rustc/Cargo.toml`) compiler workspace for
# `riscv64gc-unknown-linux-gnu` using a custom `-Z codegen-backend` shared
# library (`librustc_codegen_anneal.so`).
#
# Key invariants enforced by this recipe:
# 1. Target-scoped `CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS` routes
#    ONLY target crates (`riscv64gc-unknown-linux-gnu`) through
#    `librustc_codegen_anneal.so` and `-C panic=abort`, while host build scripts
#    (`build.rs`) and host proc-macros (`rustc_macros`, `serde_derive`, etc.)
#    compile with the host LLVM backend (`x86_64-unknown-linux-gnu`) so Cargo
#    can execute and `dlopen` them during compilation.
# 2. `--no-default-features` disables `rustc`'s default features (`llvm` and
#    `jemalloc` in `compiler/rustc/Cargo.toml` and
#    `compiler/rustc_driver_impl/Cargo.toml`), pruning `rustc_codegen_llvm`
#    (`llvm-sys` C++ build) and `tikv-jemalloc-sys` (C cross-compiler build) so
#    the entire 249-crate graph is 100% pure Rust.
# 3. `-Z build-std=core,compiler_builtins,alloc,std,panic_abort,proc_macro`
#    builds the target standard library from source through
#    `librustc_codegen_anneal.so`.
# 4. Bootstrap environment variables (`RUSTC_BOOTSTRAP=1`, `CFG_RELEASE`,
#    `CFG_RELEASE_CHANNEL`, `CFG_VERSION`, `CFG_COMPILER_HOST_TRIPLE`,
#    `RUSTC_INSTALL_BINDIR`) satisfy `option_env!` / `env!` checks across
#    `rustc_interface`, `rustc_session`, `rustc_metadata`, and `rustc_driver_impl`.

set -euo pipefail

: "${RUST_SRC_DIR:?Set RUST_SRC_DIR to the rust-lang/rust checkout path}"
: "${CODEGEN_BACKEND_SO:?Set CODEGEN_BACKEND_SO to the absolute path of librustc_codegen_anneal.so}"
TARGET_DIR="${TARGET_DIR:-${RUST_SRC_DIR}/target/rv64gc-anneal}"

export RUSTC_BOOTSTRAP=1
export CFG_RELEASE="1.101.0-nightly"
export CFG_RELEASE_CHANNEL="nightly"
export CFG_VERSION="1.101.0-nightly (anneal-rv64gc)"
export CFG_COMPILER_HOST_TRIPLE="riscv64gc-unknown-linux-gnu"
export RUSTC_INSTALL_BINDIR="bin"

export CARGO_TARGET_RISCV64GC_UNKNOWN_LINUX_GNU_RUSTFLAGS="-Z codegen-backend=${CODEGEN_BACKEND_SO} -C panic=abort"

cargo build \
  --manifest-path "${RUST_SRC_DIR}/compiler/rustc/Cargo.toml" \
  --target riscv64gc-unknown-linux-gnu \
  --no-default-features \
  -Z build-std=core,compiler_builtins,alloc,std,panic_abort,proc_macro \
  --target-dir "${TARGET_DIR}"
