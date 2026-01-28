# camino-tempfile

[![camino-tempfile on crates.io](https://img.shields.io/crates/v/camino-tempfile)](https://crates.io/crates/camino-tempfile)
[![Documentation (latest release)](https://img.shields.io/badge/docs-latest%20version-brightgreen.svg)](https://docs.rs/camino-tempfile)
[![Documentation (main)](https://img.shields.io/badge/docs-main-purple.svg)](https://camino-rs.github.io/camino-tempfile/rustdoc/camino_tempfile/)
[![License (Apache 2.0)](https://img.shields.io/badge/license-Apache-green.svg)](LICENSE-APACHE)
[![License (MIT)](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE-MIT)

A secure, cross-platform, temporary file library for Rust with UTF-8 paths.

This crate is a wrapper around [`tempfile`](https://crates.io/crates/tempfile) that works with the `Utf8Path` and `Utf8PathBuf` types defined by [`camino`](https://crates.io/crates/camino). If your code mostly uses `camino`, it can be annoying to have to convert temporary paths to
`Utf8Path` over and over again. This crate manages that for you.

In addition to creating temporary files, this library also allows users to securely open multiple independent references to the same temporary file (useful for consumer/producer patterns and surprisingly difficult to implement securely).

This crate closely mirrors tempfile's interface. For extensions that provide quality-of-life improvements such as the ability to create files easily, see [`camino-tempfile-ext`](https://crates.io/crates/camino-tempfile-ext).

[Documentation](https://docs.rs/camino-tempfile)

## Usage

Add this to your Cargo.toml:

```toml
[dependencies]
camino-tempfile = "1"
```

## Example

```rust
use std::fs::File;
use std::io::{Write, Read, Seek, SeekFrom};

fn main() {
    // Write
    let mut tmpfile: File = camino_tempfile::tempfile().unwrap();
    write!(tmpfile, "Hello World!").unwrap();

    // Seek to start
    tmpfile.seek(SeekFrom::Start(0)).unwrap();

    // Read
    let mut buf = String::new();
    tmpfile.read_to_string(&mut buf).unwrap();
    assert_eq!("Hello World!", buf);
}
```

## Minimum supported Rust version (MSRV)

camino-tempfile's MSRV is **Rust 1.74**. At any time, at least the last 6 months of Rust releases will be supported.

## License

This project is available under the terms of either the [Apache 2.0 license](LICENSE-APACHE) or the [MIT
license](LICENSE-MIT).

Portions copied and adapted from [tempfile](https://github.com/Stebalien/tempfile) and used under the MIT and Apache 2.0 licenses. tempfile is copyright 2015 Steven Allen and the tempfile authors.
