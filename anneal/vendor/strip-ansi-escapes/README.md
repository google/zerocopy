![Continuous integration](https://github.com/luser/strip-ansi-escapes/workflows/Continuous%20integration/badge.svg)  [![crates.io](https://img.shields.io/crates/v/strip-ansi-escapes.svg)](https://crates.io/crates/strip-ansi-escapes) [![](https://docs.rs/strip-ansi-escapes/badge.svg)](https://docs.rs/strip-ansi-escapes)

A crate for stripping ANSI escape sequences from byte sequences.

This can be used to take output from a program that includes escape sequences and write
it somewhere that does not easily support them, such as a log file.

# Examples

The `strip` function accepts bytes and returns a `Vec` of bytes with ANSI escape sequences removed.

```rust
extern crate strip_ansi_escapes;

use std::io::{self, Write};

fn work() -> io::Result<()> {
  let bytes_with_colors = b"\x1b[32mfoo\x1b[m bar";
  let plain_bytes = strip_ansi_escapes::strip(&bytes_with_colors);
  io::stdout().write_all(&plain_bytes)?;
  Ok(())
}

fn main() {
    work().unwrap();
}
```

For writing directly to a writer, the `Writer` struct may be preferable.

```rust
extern crate strip_ansi_escapes;

use std::io::{self, Write};
use strip_ansi_escapes::Writer;

fn work() -> io::Result<()> {
  let bytes_with_colors = b"\x1b[32mfoo\x1b[m bar";
  let mut writer = Writer::new(io::stdout());
  // Only `foo bar` will be written to stdout
  writer.write_all(bytes_with_colors)?;
  Ok(())
}

fn main() {
    work().unwrap();
}
```

# License

Licensed under either of

  * Apache License, Version 2.0 ([`LICENSE-APACHE`](./LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
  * MIT license ([`LICENSE-MIT`](./LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

