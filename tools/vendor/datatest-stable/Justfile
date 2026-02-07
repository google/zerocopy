# Print a help message.
help:
    just --list


# Run `cargo hack --feature-powerset` with the given arguments.
powerset *args:
    cargo hack --feature-powerset {{args}}

# Build docs for crates and direct dependencies
rustdoc:
    @cargo tree --depth 1 -e normal --prefix none --workspace \
        | gawk '{ gsub(" v", "@", $0); printf("%s\n", $1); }' \
        | xargs printf -- '-p %s\n' \
        | RUSTC_BOOTSTRAP=1 RUSTDOCFLAGS='--cfg=doc_cfg' xargs cargo doc --no-deps --lib --all-features

    echo "/ /rustdoc/datatest_stable/ 301" > target/doc/_redirects

# Generate README.md files using `cargo-sync-rdme`.
generate-readmes:
    cargo sync-rdme --toolchain nightly --all-features

# Collect coverage, pass in `--html` to get an HTML report
coverage *args:
    cargo +nightly llvm-cov --no-report nextest --all-features
    cargo +nightly llvm-cov --no-report --doc --all-features
    cargo +nightly llvm-cov report --doctests {{args}}
