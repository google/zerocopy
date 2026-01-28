## countio

[![Build Status][action-badge]][action-url]
[![Crate Docs][docs-badge]][docs-url]
[![Crate Version][crates-badge]][crates-url]
[![Crate Coverage][coverage-badge]][coverage-url]

**Check out other `spire` projects [here](https://github.com/spire-rs).**

[action-badge]: https://img.shields.io/github/actions/workflow/status/spire-rs/countio/build.yaml?branch=main&label=build&logo=github&style=flat-square
[action-url]: https://github.com/spire-rs/countio/actions/workflows/build.yaml
[crates-badge]: https://img.shields.io/crates/v/countio.svg?logo=rust&style=flat-square
[crates-url]: https://crates.io/crates/countio
[docs-badge]: https://img.shields.io/docsrs/countio?logo=Docs.rs&style=flat-square
[docs-url]: http://docs.rs/countio
[coverage-badge]: https://img.shields.io/codecov/c/github/spire-rs/countio?logo=codecov&logoColor=white&style=flat-square
[coverage-url]: https://app.codecov.io/gh/spire-rs/countio

The wrapper struct to enable byte counting for `std::io::{Read, Write, Seek}`
and its asynchronous variants from `futures` and `tokio` crates.

### Features

- `std` to enable `std::io::{Read, Write, Seek}`. **Enabled by default**.
- `futures` to enable `futures_io::{AsyncRead, AsyncWrite, AsyncSeek}`.
- `tokio` to enable `tokio::io::{AsyncRead, AsyncWrite, AsyncSeek}`.

### Examples

- `std::io::Read`:

```rust
use std::io::{BufRead, BufReader, Result};
use countio::Counter;

fn main() -> Result<()> {
    let reader = "Hello World!".as_bytes();
    let reader = BufReader::new(reader);
    let mut reader = Counter::new(reader);

    let mut buf = String::new();
    let len = reader.read_line(&mut buf)?;

    assert_eq!(len, reader.reader_bytes());
    Ok(())
}
```

- `std::io::Write`:

```rust
use std::io::{BufWriter, Write, Result};
use countio::Counter;

fn main() -> Result<()> {
    let writer = Vec::new();
    let writer = BufWriter::new(writer);
    let mut writer = Counter::new(writer);

    let buf = "Hello World!".as_bytes();
    let len = writer.write(buf)?;
    writer.flush()?;

    assert_eq!(len, writer.writer_bytes());
    Ok(())
}
```

### Other crates

- [SOF3/count-write](https://crates.io/crates/count-write)
