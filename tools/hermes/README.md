# Hermes

Hermes is a tool for "literate verification" of Rust code. Write safety comments in Lean, and Hermes will verify them automatically.

Hermes is designed for use by humans and coding agents. We have [demonstrated](https://drive.google.com/file/d/1GAKwocNh_XDR0LOl9i3_GFrSLnsd4zHT/view?usp=sharing)[^1] that Antigravity can author `unsafe` Rust code and prove its soundness using Hermes.

The [main design document](docs/design/design.md) motivates Hermes and describes its design in detail. The `docs/design` directory contains that and other design documents.

[^1]: This link is internal to Google, although we hope to share it publicly soon.

## Installation

Install Hermes:

```
cargo install cargo-hermes@0.1.0-alpha.3
```

Optionally, install the Charon and Aeneas toolchains from pre-built binaries:

```
cargo hermes setup
```
