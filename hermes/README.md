# Hermes

Hermes is a tool for "literate verification" of Rust code. Write safety comments in Lean, and Hermes will verify them automatically.

Hermes is designed for use by humans and coding agents. We have [demonstrated](https://drive.google.com/file/d/1areyf438L0izETTHj7PRMnoSHSX4kM29/view?usp=sharing) that Antigravity can author `unsafe` Rust code and prove its soundness using Hermes.

The [main design document](docs/design/design.md) motivates Hermes and describes its design in detail. The `docs/design` directory contains that and other design documents.

## Installation

Install Hermes:

```
cargo install cargo-hermes@0.1.0-alpha.8
```

Optionally, install the Charon and Aeneas toolchains from pre-built binaries:

```
cargo hermes setup
```
