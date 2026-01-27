_list:
    @just --list

msrv := ```
    cargo metadata --format-version=1 \
    | jq -r 'first(.packages[] | select(.source == null and .rust_version)) | .rust_version' \
    | sed -E 's/^1\.([0-9]{2})$/1\.\1\.0/'
```
msrv_rustup := "+" + msrv

# Check project.
[group("lint")]
check: && clippy
    just --unstable --fmt --check
    # fd --hidden -e=toml --exec-batch taplo format --check
    # fd --hidden -e=toml --exec-batch taplo lint
    # fd --hidden --type=file -e=md -e=yml --exec-batch prettier --check
    cargo +nightly fmt -- --check

# Format project.
[group("lint")]
fmt:
    just --unstable --fmt
    # fd --hidden -e=toml --exec-batch taplo format
    # fd --hidden --type=file -e=md -e=yml --exec-batch prettier --write
    cargo +nightly fmt

# Update READMEs from crate root documentation.
[group("lint")]
update-readme:
    cargo rdme --force
    npx -y prettier --write README.md

# Lint workspace with Clippy.
[group("lint")]
clippy:
    cargo clippy --workspace --all-targets --no-default-features
    cargo clippy --workspace --all-targets --all-features

# Test workspace.
[group("test")]
test toolchain="":
    cargo {{ toolchain }} nextest run --workspace --no-default-features
    cargo {{ toolchain }} nextest run --workspace --all-features
    cargo {{ toolchain }} test --doc --workspace --all-features
    RUSTDOCFLAGS="-D warnings" cargo {{ toolchain }} doc --workspace --no-deps --all-features

# Downgrade dev-dependencies necessary to run MSRV checks/tests.
[private]
downgrade-for-msrv:
    cargo update -p=divan --precise=0.1.15
    cargo update -p=clap --precise=4.3.24
    cargo update -p=clap_lex --precise=0.5.0

# Test workspace using MSRV.
[group("test")]
test-msrv: downgrade-for-msrv (test msrv_rustup)

# Test workspace and generate Codecov coverage file
[group("test")]
test-coverage-codecov toolchain="":
    cargo {{ toolchain }} llvm-cov --workspace --all-features --codecov --output-path codecov.json

# Test workspace and generate LCOV coverage file
[group("test")]
test-coverage-lcov toolchain="":
    cargo {{ toolchain }} llvm-cov --workspace --all-features --lcov --output-path lcov.info

# Build crate for a no-std target.
build-no-std:
    cargo build --target=thumbv6m-none-eabi --manifest-path=./ensure-no-std/Cargo.toml

# Document crates in workspace.
[group("docs")]
doc *args:
    RUSTDOCFLAGS="--cfg=docsrs -Dwarnings" cargo +nightly doc --workspace --all-features {{ args }}
