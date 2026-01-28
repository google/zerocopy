.PHONY: all
all: check test

.PHONY: build
build:
	@cargo build --all

.PHONY: doc
doc:
	@cargo doc

.PHONY: check
check:
	@cargo check --all

.PHONY: test
test:
	@cargo test --all

.PHONY: format
format:
	@rustup component add rustfmt 2> /dev/null
	@cargo fmt --all

.PHONY: format-check
format-check:
	@rustup component add rustfmt 2> /dev/null
	@cargo fmt --all -- --check

.PHONY: lint
lint:
	@rustup component add clippy 2> /dev/null
	@cargo clippy --all -- -F clippy::dbg-macro -D warnings
