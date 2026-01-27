# debug-ignore

[![debug-ignore on crates.io](https://img.shields.io/crates/v/debug-ignore)](https://crates.io/crates/debug-ignore)
[![Documentation (latest release)](https://docs.rs/debug-ignore/badge.svg)](https://docs.rs/debug-ignore/)
[![Documentation (main)](https://img.shields.io/badge/docs-main-brightgreen)](https://sunshowers-code.github.io/debug-ignore/rustdoc/debug_ignore/)
[![License](https://img.shields.io/badge/license-Apache-green.svg)](LICENSE-APACHE)
[![License](https://img.shields.io/badge/license-MIT-green.svg)](LICENSE-MIT)

This library contains `DebugIgnore`, a newtype wrapper that causes a field to be skipped while
printing out `Debug` output.

## Examples

```rust
use debug_ignore::DebugIgnore;

// Some structs have many fields with large `Debug` implementations.
#[derive(Debug)]
struct InnerStructWithLotsOfDebugInfo {
    field: &'static str,
    // ...
}

#[derive(Debug)]
pub struct PublicStruct {
    inner: DebugIgnore<InnerStructWithLotsOfDebugInfo>,
}

impl PublicStruct {
    pub fn new() -> Self {
        Self {
            // DebugIgnore<T> has a `From<T>` impl for the inner type; you can also construct
            // one explicitly.
            inner: InnerStructWithLotsOfDebugInfo { field: "field", /* ... */ }.into(),
        }
    }
}

let x = PublicStruct::new();
assert_eq!(format!("{:?}", x), "PublicStruct { inner: ... }");

// Fields within inner can still be accessed through the Deref impl.
assert_eq!(x.inner.field, "field");
```

## Why?

Some structs have many fields with large `Debug` implementations. It can be really annoying to
go through a ton of usually irrelevant `Debug` output.

`DebugIgnore` is a zero-cost, zero-compile-time way to achieve a `Debug` impl that skips over a
field.

## Optional features

`serde`: `serde` support with `#[serde(transparent)]`.

## Rust version support

The MSRV is **Rust 1.34** though this crate likely builds with older versions. This crate is
too trivial to require anything more recent.

Optional features may require newer versions of Rust.

## Alternatives

* Implement `Debug` by hand.
* [`derivative`](https://crates.io/crates/derivative) has greater control over the behavior of
  `Debug` impls, at the cost of a compile-time proc-macro dependency.

## Contributing

Pull requests are welcome! Please follow the [code of conduct](CODE_OF_CONDUCT.md).

## License

This project is available under the terms of either the [Apache 2.0 license](LICENSE-APACHE) or the [MIT
license](LICENSE-MIT).

<!--
README.md is generated from README.tpl by cargo readme. To regenerate:

cargo install cargo-readme
cargo readme > README.md
-->
