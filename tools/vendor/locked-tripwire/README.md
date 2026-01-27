# `--locked` tripwire

The goal of this crate is to prevent the use of `cargo install xxx` without `--locked`.

This crate is built for the needs of [cargo-nextest](https://nexte.st/), though anyone in the ecosystem who wishes to have the same behavior is welcome to use it.

## Why is a plain `cargo install` bad?

By default, `cargo install xxx` pulls in the latest semver-compatible versions of dependencies, ignoring the bundled `Cargo.lock` file ([rust-lang/cargo#7169](https://github.com/rust-lang/cargo/issues/7169)). This works most of the time. But sometimes, innocuous updates to dependencies can break the build anyway.

For example, pulling a dependency into scope can cause [`AsRef::as_ref`](https://doc.rust-lang.org/std/convert/trait.AsRef.html) to [no longer be unique](https://github.com/nextest-rs/nextest/issues/2990).

For this reason, many projects including cargo-nextest [clearly document](https://nexte.st/docs/installation/from-source/) that a plain `cargo install cargo-nextest` without `--locked` is not supported. But many users may miss this documentation and file issues when it fails, increasing maintainer support load.

## How it works

This crate has two versions: 0.1.1 and 0.1.1002. Version 0.1.1 is empty, while version 0.1.1002 has a `compile_error!` statement in it with a helpful message.

In your top-level binary crate's `Cargo.lock`, add:

```toml
[dependencies]
locked-tripwire = "0.1.1"
```

Then, run `cargo update locked-tripwire --precise 0.1.1`.

When used without `--locked`, `cargo install xxx` will update this crate to 0.1.1002, causing the tripwire to be triggered.

When used with `--locked`, `cargo install xxx` will preserve the 0.1.1 version of this crate.

## I need a bugfix from an updated dependency

We understand and sympathize with this use case, and would consider supporting an unlocked build if it were not the default. As it stands, though, the downsides of the default `cargo install` being unlocked outweigh the upsides.

If you urgently need a bugfix, you are always welcome to patch out this dependency locally.

If and when `cargo install --locked` becomes the default, even on an opt-in per-binary basis, we'll remove this hack.

## Features

The `nextest` feature customizes the error message to be cargo-nextest specific.

## License

This project is available under the terms of either the [Apache 2.0 license](LICENSE-APACHE) or the [MIT
license](LICENSE-MIT).
