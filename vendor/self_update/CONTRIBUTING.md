### Contributing


After making changes:

- Run tests: `cargo test`
- Run example file as a simple integration test: `cargo run --example github`
- Run cargo-fmt:
    ```
    # make sure rust-fmt is installed
    rustup self update
    rustup component add rustfmt-preview clippy

    # check
    cargo fmt --all -- --check
    cargo clippy --all-targets --all-features --examples --tests
    # apply fixes
    cargo fmt --all
    ```
- The project README.md is generated from the crate docs in `src/lib.rs` using `cargo-readme`
    - All readme-content should be added/edited in the `src/lib` crate-level doc section,
      and then the `readme.sh` script should be run to update the README.md.
    ```
    cargo install cargo-readme
    ./readme.sh
    ```
- Update the CHANGELOG.md `unreleased` section with a summary of your changes
- Open a PR to trigger CI builds for all platforms


*Thank you!*
