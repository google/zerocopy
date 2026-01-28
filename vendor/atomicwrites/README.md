# rust-atomicwrites

[![Build Status](https://travis-ci.org/untitaker/rust-atomicwrites.svg?branch=master)](https://travis-ci.org/untitaker/rust-atomicwrites)
[![Windows build status](https://ci.appveyor.com/api/projects/status/h6642x2d54xl0sev?svg=true)](https://ci.appveyor.com/project/untitaker/rust-atomicwrites)

- [Documentation](https://docs.rs/crate/atomicwrites)
- [Repository](https://github.com/untitaker/rust-atomicwrites)
- [Crates.io](https://crates.io/crates/atomicwrites)

Atomic file-writes. Works on both POSIX and Windows.

The basic idea is to write to temporary files (in the same file
system), and move them when done writing.
This avoids the problem of two programs writing to the same file. For
`AllowOverwrite`, `rename` is used. For `DisallowOverwrite`, `link + unlink` is
used instead to raise errors when the target path already exists.

This is mostly a port of the same-named [Python package](https://github.com/untitaker/python-atomicwrites).

## Example

```rust
use atomicwrites::{AtomicFile,DisallowOverwrite};

let af = AtomicFile::new("foo", DisallowOverwrite);
af.write(|f| {
    f.write_all(b"HELLO")
})?;
```

## Alternatives

- [tempfile](https://github.com/Stebalien/tempfile) has a `persist` method doing the same thing.

## License

Licensed under MIT, see ``LICENSE``.
