## ByteSize

<!-- prettier-ignore-start -->

[![crates.io](https://img.shields.io/crates/v/bytesize?label=latest)](https://crates.io/crates/bytesize)
[![Documentation](https://docs.rs/bytesize/badge.svg?version=2.3.1)](https://docs.rs/bytesize/2.3.1)
![Version](https://img.shields.io/badge/rustc-1.70+-ab6000.svg)
![Apache 2.0 licensed](https://img.shields.io/crates/l/bytesize.svg)
<br />
[![Dependency Status](https://deps.rs/crate/bytesize/2.3.1/status.svg)](https://deps.rs/crate/bytesize/2.3.1)
[![Download](https://img.shields.io/crates/d/bytesize.svg)](https://crates.io/crates/bytesize)

<!-- prettier-ignore-end -->

<!-- cargo-rdme start -->

`ByteSize` is a semantic wrapper for byte count representations.

Features:

- Pre-defined constants for various size units (e.g., B, Kb, Kib, Mb, Mib, Gb, Gib, ... PB).
- `ByteSize` type which presents size units convertible to different size units.
- Arithmetic operations for `ByteSize`.
- `FromStr` impl for `ByteSize`, allowing for parsing string size representations like "1.5KiB" and "521TiB".
- Serde support for binary and human-readable deserializers like JSON.

### Examples

Construction using SI or IEC helpers.

```rust
use bytesize::ByteSize;

assert!(ByteSize::kib(4) > ByteSize::kb(4));
```

Display as human-readable string.

```rust
use bytesize::ByteSize;

assert_eq!("518.0 GiB", ByteSize::gib(518).display().iec().to_string());
assert_eq!("556.2 GB", ByteSize::gib(518).display().si().to_string());
assert_eq!("518.0G", ByteSize::gib(518).display().iec_short().to_string());
```

Arithmetic operations are supported.

```rust
use bytesize::ByteSize;

let plus = ByteSize::mb(1) + ByteSize::kb(100);
println!("{plus}");

let minus = ByteSize::tb(1) - ByteSize::gb(4);
assert_eq!(ByteSize::gb(996), minus);
```

<!-- cargo-rdme end -->
