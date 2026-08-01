# Supported configurations

Let `r` denote a released stable Rust toolchain, ordered by its semantic
version. This source snapshot supports the symbolic release interval

```text
1.84.0 <= r <= 1.86.0
```

The interval means every stable Rust release in that closed interval, not only
the `.0` releases. In particular, Rust 1.85.1 is expressly supported.

The supported target triples are:

- `x86_64-unknown-linux-gnu`;
- `aarch64-apple-darwin`; and
- `wasm32-unknown-unknown`.

Both states of the `telemetry` feature are supported. Every combination of a
release in the interval, a listed target, and a feature state is supported in
every Cargo profile, with either state of debug assertions.

`Cargo.toml` states the minimum compiler accepted by Cargo. This document,
including its upper cutoff, is the project's support commitment.

